/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XDRS

 Create Date:    5/3/2011
 Design Name:    xdrs demo top

 *******************************************************************/

`timescale 1ns/1ps

module xdrs
(

);

//-------------------------------------------------------------------
// Clocks and resets
//-------------------------------------------------------------------

	reg rstn;
	initial begin rstn = 1'b0; #1_000 rstn = 1'b1; end

	reg clk;
	initial begin clk = 1'b0; end
	always begin #5 clk = ~clk; end

	/* icapi interface */
	wire          rc_start        ;
	wire   [31:0] rc_baddr        ;
	wire   [31:0] rc_bsize        ;
	wire          rc_done         ;

	/* reconfiguration-add-on interface */
	wire          rc0_reqn   , rc1_reqn   , rc2_reqn   , rc3_reqn   ;
	wire          rc0_ackn   , rc1_ackn   , rc2_ackn   , rc3_ackn   ;
	wire          rc0_rstn   , rc1_rstn   , rc2_rstn   , rc3_rstn   ;
	wire          rc0_clk    , rc1_clk    , rc2_clk    , rc3_clk    ;
	wire          rc0_reconfn, rc1_reconfn, rc2_reconfn, rc3_reconfn;

	/* producer consumer interface */
	wire          pc0_rr0_prdy, rr0_rr1_prdy, rr1_rr2_prdy, rr2_pc0_prdy;
	wire          rr0_pc0_crdy, rr1_rr0_crdy, rr2_rr1_crdy, pc0_rr2_crdy;
	wire          rr0_pc0_cerr, rr1_rr0_cerr, rr2_rr1_cerr, pc0_rr2_cerr;
	wire   [31:0] pc0_rr0_data, rr0_rr1_data, rr1_rr2_data, rr2_pc0_data;
	
	/* xbus master interface */
	wire          ma0_req   , ma1_req   , ma2_req   , ma3_req    ;
	wire          xbm0_gnt  , xbm1_gnt  , xbm2_gnt  , xbm3_gnt   ;
	wire          ma0_select, ma1_select, ma2_select, ma3_select ;
	wire   [31:0] ma0_addr  , ma1_addr  , ma2_addr  , ma3_addr   ;
	wire   [31:0] ma0_data  , ma1_data  , ma2_data  , ma3_data   ;
	wire          ma0_rnw   , ma1_rnw   , ma2_rnw   , ma3_rnw    ;
	wire   [3:0]  ma0_be    , ma1_be    , ma2_be    , ma3_be     ;
	wire          xbm0_ack  , xbm1_ack  , xbm2_ack  , xbm3_ack   ;
	wire   [31:0] xbm0_data , xbm1_data , xbm2_data , xbm3_data  ;
	
	/* xbus slave interface */
	wire          xbs_select      ;
	wire   [31:0] xbs_addr        ;
	wire   [31:0] xbs_data        ;
	wire          xbs_rnw         ;
	wire   [3:0]  xbs_be          ;
	wire          sl_ack          ;
	wire   [31:0] sl_data         ;

//-------------------------------------------------------------------
// Application Layer:
// (1) producer/consumer (application master)
// (2) reconfigurable region + isolator (application slave)
//-------------------------------------------------------------------

	/* producer & consumer */
	prodcons pc_0 (
		.clk              (clk                ),
		.rstn             (rstn               ),
		//-- producer/consumer thread (producer consumer interface)----
		.p_prdy           (pc0_rr0_prdy       ),
		.p_crdy           (rr0_pc0_crdy       ),
		.p_cerr           (rr0_pc0_cerr       ),
		.p_data           (pc0_rr0_data       ),
		
		.c_prdy           (rr2_pc0_prdy       ),
		.c_crdy           (pc0_rr2_crdy       ),
		.c_cerr           (pc0_rr2_cerr       ),
		.c_data           (rr2_pc0_data       ),
		
		//-- dummy memory traffic thread (xbus master interface)----
		.ma_req           (ma0_req            ),
		.xbm_gnt          (xbm0_gnt           ),
		.ma_select        (ma0_select         ),
		.ma_addr          (ma0_addr           ),
		.ma_data          (ma0_data           ),
		.ma_rnw           (ma0_rnw            ),
		.ma_be            (ma0_be             ),
		.xbm_ack          (xbm0_ack           ),
		.xbm_data         (xbm0_data          )
	);

	/* reconfigurable region 0 & its isolation logic */
	region_wrapper #(
		.RRID             (0)
	)  region_0 (
		.clk              (rc0_clk            ),
		.rstn             (rc0_rstn           ),
		
		//-- to/from producer consumers----
		.p_prdy           (rr0_rr1_prdy       ),
		.p_crdy           (rr1_rr0_crdy       ),
		.p_cerr           (rr1_rr0_cerr       ),
		.p_data           (rr0_rr1_data       ),
		
		.c_prdy           (pc0_rr0_prdy       ),
		.c_crdy           (rr0_pc0_crdy       ),
		.c_cerr           (rr0_pc0_cerr       ),
		.c_data           (pc0_rr0_data       ),
		
		//-- to/from reconfiguration manager----
		.rc_reqn          (rc0_reqn           ),
		.rc_ackn          (rc0_ackn           ),
		.is_reconfn       (rc0_reconfn        )
	);

	/* reconfigurable region 1 & its isolation logic */
	region_wrapper #(
		.RRID             (1)
	)  region_1 (
		.clk              (rc1_clk            ),
		.rstn             (rc1_rstn           ),
		
		//-- to/from producer consumers----
		.p_prdy           (rr1_rr2_prdy       ),
		.p_crdy           (rr2_rr1_crdy       ),
		.p_cerr           (rr2_rr1_cerr       ),
		.p_data           (rr1_rr2_data       ),
		
		.c_prdy           (rr0_rr1_prdy        ),
		.c_crdy           (rr1_rr0_crdy        ),
		.c_cerr           (rr1_rr0_cerr        ),
		.c_data           (rr0_rr1_data        ),
		
		//-- to/from reconfiguration manager----
		.rc_reqn          (rc1_reqn           ),
		.rc_ackn          (rc1_ackn           ),
		.is_reconfn       (rc1_reconfn        )
	);
	
	/* reconfigurable region 2 & its isolation logic */
	region_wrapper #(
		.RRID             (2)
	)  region_2 (
		.clk              (rc2_clk            ),
		.rstn             (rc2_rstn           ),
		
		//-- to/from producer consumers----
		.p_prdy           (rr2_pc0_prdy       ),
		.p_crdy           (pc0_rr2_crdy       ),
		.p_cerr           (pc0_rr2_cerr       ),
		.p_data           (rr2_pc0_data       ),
		
		.c_prdy           (rr1_rr2_prdy        ),
		.c_crdy           (rr2_rr1_crdy        ),
		.c_cerr           (rr2_rr1_cerr        ),
		.c_data           (rr1_rr2_data        ),
		
		//-- to/from reconfiguration manager----
		.rc_reqn          (rc2_reqn           ),
		.rc_ackn          (rc2_ackn           ),
		.is_reconfn       (rc2_reconfn        )
	);

//-------------------------------------------------------------------
// Reconfiguration Layer:
// (1) manager (reconfiguration master)
// (2) icapi (reconfiguration slave)
//-------------------------------------------------------------------

	/* reconfiguration manager */
	manager mgr_0 (
		.clk              (clk                ),
		.rstn             (rstn               ),
		//-- reconfiguration manager thread (icapi interface)----
		.rc_start         (rc_start           ),
		.rc_bop           (rc_bop             ),
		.rc_baddr         (rc_baddr           ),
		.rc_bsize         (rc_bsize           ),
		.rc_done          (rc_done            ),
		//-- reconfiguration manager thread (reconfiguration-add-on interface)----
		.rc0_reqn         (rc0_reqn           ),
		.rc0_ackn         (rc0_ackn           ),
		.rc0_clk          (rc0_clk            ),
		.rc0_rstn         (rc0_rstn           ),
		.rc0_reconfn      (rc0_reconfn        ),
		.rc1_reqn         (rc1_reqn           ),
		.rc1_ackn         (rc1_ackn           ),
		.rc1_clk          (rc1_clk            ),
		.rc1_rstn         (rc1_rstn           ),
		.rc1_reconfn      (rc1_reconfn        ),
		.rc2_reqn         (rc2_reqn           ),
		.rc2_ackn         (rc2_ackn           ),
		.rc2_clk          (rc2_clk            ),
		.rc2_rstn         (rc2_rstn           ),
		.rc2_reconfn      (rc2_reconfn        ),
		.rc3_reqn         (/* not-connected */),
		.rc3_ackn         (1'b1               ),
		.rc3_clk          (/* not-connected */),
		.rc3_rstn         (/* not-connected */),
		.rc3_reconfn      (/* not-connected */)
	);

	/* icap interface: icapi */
	icapi icapi_0 (
		.clk              (clk                ),
		.rstn             (rstn               ),
		//-- reconfiguration manager thread (icapi interface)----
		.rc_start         (rc_start           ),
		.rc_bop           (rc_bop             ),
		.rc_baddr         (rc_baddr           ),
		.rc_bsize         (rc_bsize           ),
		.rc_done          (rc_done            ),
		//-- bitstream traffic (xbus master interface)----
		.ma_req           (ma3_req            ),
		.xbm_gnt          (xbm3_gnt           ),
		.ma_select        (ma3_select         ),
		.ma_addr          (ma3_addr           ),
		.ma_data          (ma3_data           ),
		.ma_rnw           (ma3_rnw            ),
		.ma_be            (ma3_be             ),
		.xbm_ack          (xbm3_ack           ),
		.xbm_data         (xbm3_data          )
	);

//-------------------------------------------------------------------
// Shared Datapath: arbiter + memory
//-------------------------------------------------------------------

	/* storage device/memory: memctrl */
	memctrl mem_0(
		.clk              (clk                ),
		.rstn             (rstn               ),
		//-- to/from xbus slave (xbus slave interface)----
		.xbs_select       (xbs_select         ),
		.xbs_addr         (xbs_addr           ),
		.xbs_data         (xbs_data           ),
		.xbs_rnw          (xbs_rnw            ),
		.xbs_be           (xbs_be             ),
		.sl_ack           (sl_ack             ),
		.sl_data          (sl_data            )
	);

	/* arbiter: xbuscore */
	xbuscore xbc_0(
		.clk              (clk                ),
		.rstn             (rstn               ),
		//-- to/from xbus master0 (xbus master interface)----
		.ma0_req          (ma0_req            ),
		.xbm0_gnt         (xbm0_gnt           ),
		.ma0_select       (ma0_select         ),
		.ma0_addr         (ma0_addr           ),
		.ma0_data         (ma0_data           ),
		.ma0_rnw          (ma0_rnw            ),
		.ma0_be           (ma0_be             ),
		.xbm0_ack         (xbm0_ack           ),
		.xbm0_data        (xbm0_data          ),
		//-- to/from xbus master1 (xbus master interface)----
		.ma1_req          (1'b0               ),
		.xbm1_gnt         (/* not-connected */),
		.ma1_select       (1'b0               ),
		.ma1_addr         (32'b0              ),
		.ma1_data         (32'b0              ),
		.ma1_rnw          (1'b0               ),
		.ma1_be           (4'b0               ),
		.xbm1_ack         (/* not-connected */),
		.xbm1_data        (/* not-connected */),
		//-- to/from xbus master2 (xbus master interface)----
		.ma2_req          (ma2_req            ),
		.xbm2_gnt         (xbm2_gnt           ),
		.ma2_select       (ma2_select         ),
		.ma2_addr         (ma2_addr           ),
		.ma2_data         (ma2_data           ),
		.ma2_rnw          (ma2_rnw            ),
		.ma2_be           (ma2_be             ),
		.xbm2_ack         (xbm2_ack           ),
		.xbm2_data        (xbm2_data          ),
		//-- to/from xbus master3 (xbus master interface)----
		.ma3_req          (ma3_req            ),
		.xbm3_gnt         (xbm3_gnt           ),
		.ma3_select       (ma3_select         ),
		.ma3_addr         (ma3_addr           ),
		.ma3_data         (ma3_data           ),
		.ma3_rnw          (ma3_rnw            ),
		.ma3_be           (ma3_be             ),
		.xbm3_ack         (xbm3_ack           ),
		.xbm3_data        (xbm3_data          ),
		//-- to/from xbus slave (xbus slave interface)----
		.xbs_select       (xbs_select         ),
		.xbs_addr         (xbs_addr           ),
		.xbs_data         (xbs_data           ),
		.xbs_rnw          (xbs_rnw            ),
		.xbs_be           (xbs_be             ),
		.sl_ack           (sl_ack             ),
		.sl_data          (sl_data            )
	);

//-------------------------------------------------------------------
// Simulation-only Layer
//-------------------------------------------------------------------
	my_solyr sol_0();

//-------------------------------------------------------------------
// Running tests
//-------------------------------------------------------------------

	import ovm_pkg::*;
	import rsv_solyr_pkg::*;
	import usr_solyr_pkg::*;
	
	`define RM_0_0_ADDR 32'h100
	`define RM_0_0_SIZE 16

	`define RM_0_1_ADDR 32'h200
	`define RM_0_1_SIZE 16
	
	`define RM_1_0_ADDR 32'hc00
	`define RM_1_0_SIZE 16

	`define RM_1_1_ADDR 32'hd00
	`define RM_1_1_SIZE 16

	`define RM_2_0_ADDR 32'he00
	`define RM_2_0_SIZE 24

	`define RM_2_1_ADDR 32'hf00
	`define RM_2_1_SIZE 24
	
	`define DMA_WR_RM_0_0_HEADER   32'h400
	`define DMA_WR_RM_0_1_HEADER   32'h420
	`define DMA_WR_RM_1_0_HEADER   32'h440
	`define DMA_WR_RM_1_1_HEADER   32'h460
	`define DMA_WR_RM_2_0_HEADER   32'h480
	`define DMA_WR_RM_2_1_HEADER   32'h4a0
	
	`define DMA_DESYNC_SEQ   32'h500
	`define DMA_GCAPTURE_SEQ 32'h520
	`define DMA_GRESTORE_SEQ 32'h540
	`define DMA_WR_MSK_1_SEQ 32'h560
	`define DMA_WR_MSK_0_SEQ 32'h580

	`define SBT_HEADER_SIZE 16
	`define SBT_SEQ_SIZE 16
	
	`define DMA_BUFFER 32'h800

	`define DMA_WCFG 1'b1
	`define DMA_RCFG 1'b0

	`define ONE_CYCLE_DELAY 10ns
	
	`include "tdpr_random.sv"
	`include "tdpr_streaming.sv"

endmodule
