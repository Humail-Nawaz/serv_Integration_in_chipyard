package chipyard

import chisel3._

import org.chipsalliance.cde.config.{Config}

// ---------------------
// VexiiRiscv Configs
// ---------------------

class ServConfig extends Config(
  new serv.WithNServCores(1) ++
  new chipyard.config.AbstractConfig)
