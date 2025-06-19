
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// SERV Tile Wrapper
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

package serv

import chisel3._
import chisel3.util._
import chisel3.experimental.{IntParam, StringParam, RawParam}


import org.chipsalliance.cde.config._
import freechips.rocketchip.subsystem._
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.devices.tilelink._
import freechips.rocketchip.rocket._
import freechips.rocketchip.subsystem.{RocketCrossingParams}
import freechips.rocketchip.tilelink._
import freechips.rocketchip.interrupts._
import freechips.rocketchip.util._
import freechips.rocketchip.tile._
import freechips.rocketchip.prci._
import freechips.rocketchip.amba.axi4._


case class ServCoreParams(
  val bootFreqHz: BigInt = BigInt(32000000),
  val xLen = 32
  val pmpEnable: Int = 0,
  val pmpGranularity: Int = 0,
  val pmpNumRegions: Int = 0
) extends CoreParams {
  val useVM: Boolean = false
  val useHypervisor: Boolean = false
  val useUser: Boolean = true
  val useSupervisor: Boolean = false
  val useDebug: Boolean = false
  val useAtomics: Boolean = false
  val useAtomicsOnlyForIO: Boolean = false
  val useCompressed: Boolean = false
  override val useVector: Boolean = false
  val useSCIE: Boolean = false
  val useRVE: Boolean = false
  val mulDiv: Option[MulDivParams] = None
  val fpu: Option[FPUParams] = None //floating point not supported
  val fetchWidth: Int = 1
  val decodeWidth: Int = 1
  val retireWidth: Int = 1
  val instBits: Int =  32
  val nLocalInterrupts: Int = 1
  val nPMPs: Int = 0
  val nBreakpoints: Int = 0
  val useBPWatch: Boolean = false
  val nPerfCounters: Int = 0
  val haveBasicCounters: Boolean = true
  val haveFSDirty: Boolean = false
  val misaWritable: Boolean = false
  val haveCFlush: Boolean = false
  val nL2TLBEntries: Int = 0
  val mtvecInit: Option[BigInt] = Some(0)
  val mtvecWritable: Boolean = false
  val nL2TLBWays: Int = 0
  val lrscCycles: Int = 80
  // SERV SPECIFIC
  val aw_b: Int = 12
  val with_csr_b: Boolean = true
  val memsize: Int = 8192
  val sim_b: Boolean = false
  val memfile_b: String = ""
  val reset_strategy: String = "MINI"
}

case class ServTileAttachParams(
  tileParams: ServTileParams,
  crossingParams: RocketCrossingParams
) extends CanAttachTile {
  type TileType = ServTile
  val lookup = PriorityMuxHartIdFromSeq(Seq(tileParams))
}

case class ServTileParams(
  name: Option[String] = Some("serv_tile"),
  tileId: Int = 0,
  val core: ServCoreParams = ServCoreParams()
) extends InstantiableTileParams[ServTile]
{
  val beuAddr: Option[BigInt] = None
  val blockerCtrlAddr: Option[BigInt] = None
  val btb: Option[BTBParams] = None
  val boundaryBuffers: Boolean = false
  val dcache: Option[DCacheParams] = None //no dcache
  val icache: Option[ICacheParams] = None //no icache -- Bit serial processing
  val clockSinkParams: ClockSinkParameters = ClockSinkParameters()


  def instantiate(crossing: HierarchicalElementCrossingParamsLike, lookup: LookupByHartIdImpl)(implicit p: Parameters): ServTile = {
    new ServTile(this, crossing, lookup)
  }

  val baseName = name.getOrElse("serv_tile")
  val uniqueName = s"${baseName}_$tileId"
} 

class ServTile private(
  val servParams: ServTileParams,
  crossing: ClockCrossingType,
  lookup: LookupByHartIdImpl,
  q: Parameters)
  extends BaseTile(servParams, crossing, lookup, q)
  with SinksExternalInterrupts
  with SourcesExternalNotifications
{

  def this(params: ServTileParams, crossing: HierarchicalElementCrossingParamsLike, lookup: LookupByHartIdImpl)(implicit p: Parameters) =
    this(params, crossing.crossingType, lookup, p)

  //TL nodes
  val intOutwardNode = None   
  val masterNode = visibilityNode          // Master interface — TL visibility
  val slaveNode  = TLIdentityNode()        // Slave node for MMIO

  val beatBytes = p(PeripheryBusKey).beatBytes

  tlOtherMastersNode := tlMasterXbar.node
  masterNode :=* tlOtherMastersNode
  DisableMonitors { implicit p => tlSlaveXbar.node :*= slaveNode }


  // Required entry of CPU device in the device tree for interrupt purpose
  val cpuDevice: SimpleDevice = new SimpleDevice("cpu", Seq("OlofKindgren,serv", "riscv")) {
    override def parent = Some(ResourceAnchors.cpus)
    override def describe(resources: ResourceBindings): Description = {
      val Description(name, mapping) = super.describe(resources)
      Description(name, mapping ++
                        cpuProperties ++
                        nextLevelCacheProperty ++
                        tileProperties)
    }
  }

  ResourceBinding {
    Resource(cpuDevice, "reg").bind(ResourceAddress(tileId))
  }

  }


override def makeMasterBoundaryBuffers(crossing: ClockCrossingType)(implicit p: Parameters) = crossing match {
    case _: RationalCrossing =>
      if (!servParams.boundaryBuffers) TLBuffer(BufferParams.none)
      else TLBuffer(BufferParams.none, BufferParams.flow, BufferParams.none, BufferParams.flow, BufferParams(1))
    case _ => TLBuffer(BufferParams.none)
  }

override def makeSlaveBoundaryBuffers(crossing: ClockCrossingType)(implicit p: Parameters) =
  TLBuffer(BufferParams.none)



override lazy val module = new ServTileModuleImp(this)


  val portName = "serv-axi4-master"
  val idBits = 4

  val ServAXI4MNode = AXI4MasterNode(
    Seq(AXI4MasterPortParameters(
      masters = Seq(AXI4MasterParameters(
        name = portName,
        id = IdRange(0, 1 << idBits))))))

  val memoryTap = TLIdentityNode()



  // ------------------------- MASTER NODE ---------------------------- //
  // tlMasterXbar is the bus crossbar to be used when this core / tile is acting as a master; otherwise, use tlSlaveXBar


  (tlMasterXbar.node  
    := memoryTap
    := TLBuffer()
    := TLFIFOFixer(TLFIFOFixer.all) // fix FIFO ordering
    := TLWidthWidget(masterPortBeatBytes) // reduce size of TL
    := AXI4ToTL() // convert to TL
    := AXI4UserYanker(Some(2)) // remove user field on AXI interface. need but in reality user intf. not needed
    := AXI4Fragmenter() // deal with multi-beat xacts
    := ServAXI4MNode) // Custom SERV node.


 // ------------------------- MASTER NODE ------------------------------- //





  val portName = "serv-axi4-slave"
  val idBits = 4

  val ServAXI4SNode = AXI4SlaveNode(
    Seq(AXI4SlavePortParameters(
        slaves  = Seq(AXI4SlaveParameters(
        name    = portName,
        address = AddressSet(0x4000_0000L, 0x3FF), 
        id      = IdRange(0, 1 << idBits))))))

// -------------------------- SLAVE NODE -------------------------------- //

val slaveTLNode = TLIdentityNode()

(tlSlaveXbar.node 
    := ServAXI4SNode
    := AXI4Fragmenter()                 // fragment to AXI-Lite if needed
    := AXI4UserYanker()                 // strip TLToAXI4’s user field
    := AXI4Deinterleaver(beatBytes)   // re-order AXI read beats
    := TLToAXI4()                       // convert TL to AXI4
    := TLBuffer()                       // add buffering (decoupling)
    := TLWidthWidget(beatBytes)    // match beat width
    := slaveTLNode)
// -------------------------- SLAVE NODE -------------------------------- //

def connectServInterrupts(mtip: Bool) {
    val (interrupts, _) = intSinkNode.in(0)
    mtip := interrupts(1)

  }



class ServTileModuleImp(outer: ServTile) extends BaseTileModuleImp(outer){
  

  val core = Module(new ServCoreBlackbox(

    // general core params
    xLen             = outer.servParams.core.xLen,
    aw_b             = outer.servParams.core.aw_b,
    with_csr_b       = outer.servParams.core.with_csr,
    sim_b            = outer.servParams.core.sim_b,
    memsize_b        = outer.servParams.core.memsize_b,
    memfile_b        = outer.servParams.core.memfile_b,
    reset_strategy_b = outer.servParams.core.reset_strategy_b
    
     ))

  core.io.clk := clock
  core.io.rst := reset.asBool    // Check Reset --
  

  outer.connectServInterrupts(core.io.i_timer_irq)


  // connect the axi interface
  outer.ServAXI4MNode.out foreach { case (out, edgeOut) =>
    core.io.i_awmready             := out.aw.ready
    out.aw.valid                   := core.io.o_awmvalid
    out.aw.bits.addr               := core.io.o_awmaddr
    
    // unused signals
    //  assert(core.io.axi_req_o_aw_bits_region === 0.U)

    core.io.i_wmready              := out.w.ready
    out.w.valid                    := core.io.o_wmvalid
    out.w.bits.data                := core.io.o_wmdata
    out.w.bits.strb                := core.io.o_wmstrb
    
    // unused signals
    //  assert(core.io.axi_req_o_w_bits_user === 0.U)

    out.b.ready                    := core.io.o_bmready
    core.io.i_bmvalid              := out.b.valid
    core.io.i_bmresp               := out.b.bits.resp
    //core.io.axi_resp_i_b_bits_user := 0.U // unused

    core.io.i_armready             := out.ar.ready
    out.ar.valid                   := core.io.o_armvalid
    out.ar.bits.addr               := core.io.o_armaddr
    
    // unused signals if any
    
    out.r.ready                    := core.io.o_rmready
    core.io.i_rmvalid              := out.r.valid
    core.io.i_rmdata                := out.r.bits.data
    core.io.i_rmresp               := out.r.bits.resp
    core.io.i_rmlast               := out.r.bits.last
    //core.io.axi_resp_i_r_bits_user := 0.U // unused
  }
}
