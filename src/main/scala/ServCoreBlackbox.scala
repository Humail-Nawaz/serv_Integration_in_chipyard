//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// serv Tile Wrapper
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
package serv

import sys.process._

import chisel3._
import chisel3.util._
import chisel3.experimental.{IntParam, StringParam, RawParam}

import scala.collection.mutable.{ListBuffer}

class ServCoreBlackbox(
		withcsrb: Int,
		pre_register_b: Int,
		reset_strategy_b:Int,
		reset_pc_b:Int,
		mdu_b: Int,
		compressed_b: Int,
		align_b: Int,
		rf_width_b: Int,
		rf_l2d_b: Int,
    aw_b: Int)

extends BlackBox(
   Map(
	"WITH_CSR_B" -> IntParam(withcsrb),
	"PRE_REGISTER_B" -> IntParam(pre_register_b),
	"RESET_STRATEGY_B" ->IntParam(reset_strategy_b),
	"RESET_PC_B" ->IntParam(reset_pc_b),
	"MDU_B" ->IntParam(mdu_b),
	"COMPRESSED_B" ->IntParam(compressed_b),
	"ALIGN_B" ->IntParam(align_b),
	"RF_WIDTH_B" ->IntParam(rf_width_b),
	"RF_L2D_B" ->IntParam(rf_l2d_b))
	)
  with HasBlackBoxPath
  {
  	val io=IO(new Bundle{
  		val  clk=Input(Clock())
  		val  i_rst=Input(Bool())
  		val  i_timer_irq=Input(Bool())
  		val  o_ibus_adr=Output(UInt(32.W))
  		val  o_ibus_cyc=Output(Bool())
  		val  i_ibus_rdt=Input(UInt(32.W))
  		val  i_ibus_ack=Input(Bool())
  		val  o_dbus_adr=Output(UInt(32.W))
  		val  o_dbus_dat=Output(UInt(32.W))
  		val  o_dbus_sel=Output(UInt(4.W))
  		val  o_dbus_we=Output(Bool())
  		val  o_dbus_cyc=Output(Bool())
  		val  i_dbus_rdt=Input(UInt(32.W))
  		val  i_dbus_ack=Input(Bool())
  		val  o_ext_rs1=Output(UInt(32.W))
  		val  o_ext_rs2=Output(UInt(32.W))
  		val  o_ext_funct3=Output(UInt(3.W))
  		val  i_ext_rd=Input(UInt(32.W))
  		val  i_ext_ready=Input(Bool())
  		val  o_mdu_valid=Output(Bool())
  		}
  		)
    val chipyardDir = System.getProperty("user.dir")
    val servVsrcDir = s"$chipyardDir/generators/serv/src/main/resources/vsrc"

    val proc = s"make -C $servVsrcDir default"
    require (proc.! == 0, "Failed to run preprocessing step")

    // generated from preprocessing step
    addPath(s"$servVsrcDir/ServCoreBlackbox.preprocessed.v")
    
  }
