
module ServCoreBlackbox 
#(
   parameter memfile_B = "",           // Hex file to be loaded into core RAM.
   parameter memsize_B = 8192,
   parameter sim_B = 1'b0,
   parameter RESET_STRATEGY_B = "NONE",
   parameter WITH_CSR_B = 1,
   parameter AW_B       = 12

)

(
    // CORE TOP
    input   clk,
    input   rst,
    input   i_timer_irq,

    // AXI2WB -- AXI SIGNALS FROM EXTERNAL(BUS/PERIPHERAL/ADAPTER) TO BRIDGE

    // AXI address write channel
    input   [AW_B-1:0] i_awaddr,
    input   i_awvalid,
    output  o_awready,

    // AXI address read channel 
    input   [AW_B-1:0] i_araddr,
    input   i_arvalid,
    output  o_arready,

    // AXI write channel
    input   [31:0] i_wdata,
    input   [3:0] i_wstrb,
    input   i_wvalid,
    output  o_wready,

    // AXI response channel
    input   i_bready,
    output  [1:0] o_bresp,
    output  o_bvalid,
    
    // AXI read channel
    input   i_rready,
    output  [31:0] o_rdata,
    output  [1:0] o_rresp,
    output  o_rlast,
    output  o_rvalid,
    
    // ---------------------------------------------------------------- //

    // AXI2WB AXI SIGNALS FROM BRIDGE TO EXTERNAL(PERIPHERAL/ADAPTER/BUS)


    // AXI address write channel
    input   i_awmready,
    output  [AW_B-1:0] o_awmaddr,
    output  o_awmvalid,


    // AXI address read channel
    input   i_armready,
    output  [AW_B-1:0] o_armaddr,
    output  o_armvalid,

    // AXI write channel
    input  i_wmready,
    output [31:0] o_wmdata,
    output [3:0] o_wmstrb,
    output o_wmvalid,

    // AXI response channel
    input  [1:0] i_bmresp,
    input  i_bmvalid,
    output o_bmready,

    //AXI read channel
    input   [31:0] i_rmdata,
    input   [1:0] i_rmresp,
    input   i_rmlast,
    input   i_rmvalid,
    output  o_rmready


);


serv                                                  // serv here means: Serving(the convenience wrapper) plus the Bridge
#(
        .memfile(memfile_B),
        .memsize(memsize_B),
        .sim(sim_B),
        .RESET_STRATEGY(RESET_STRATEGY_B),
        .WITH_CSR(WITH_CSR_B),
        .AW(AW_B)

)

   i_serv (
        .clk          (clk),
        .rst          (rst),
        .i_timer_irq  (i_timer_irq),



        .i_awaddr     (i_awaddr),
        .i_awvalid    (i_awvalid),
        .o_awready    (o_awready),

        .i_araddr     (i_araddr),
        .i_arvalid    (i_arvalid),
        .o_arready    (o_arready),

        .i_wdata      (i_wdata),
        .i_wstrb      (i_wstrb),
        .i_wvalid     (i_wvalid),
        .o_wready     (o_wready),

        .i_bready    (i_bready),
        .o_bresp     (o_bresp),
        .o_bvalid    (o_bvalid),

        .i_rready    (i_rready),
        .o_rdata     (o_rdata),
        .o_rresp     (o_rresp),
        .o_rlast     (o_rlast),
        .o_rvalid    (o_rvalid),



        .i_awmready  (i_awmready),
        .o_awmaddr   (o_awmaddr),
        .o_awmvalid  (o_awmvalid),

        .i_armready  (i_armready),
        .o_armaddr   (o_armaddr),
        .o_armvalid  (o_armvalid),

        .i_wmready   (i_wmready),
        .o_wmdata    (o_wmdata),
        .o_wmstrb    (o_wmstrb),
        .o_wmvalid   (o_wmvalid),

        .i_bmresp    (i_bmresp),
        .i_bmvalid   (i_bmvalid),
        .o_bmready   (o_bmready),

        .i_rmdata    (i_rmdata),
        .i_rmresp    (i_rmresp),
        .i_rmlast    (i_rmlast),
        .i_rmvalid   (i_rmvalid),
        .o_rmready   (o_rmready)


    );

endmodule