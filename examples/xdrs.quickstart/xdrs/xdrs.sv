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
	wire          rc0_ackn_rr, rc1_ackn_rr, rc2_ackn_rr, rc3_ackn_rr;
	wire          rc0_rstn   , rc1_rstn   , rc2_rstn   , rc3_rstn   ;
	wire          rc0_clk    , rc1_clk    , rc2_clk    , rc3_clk    ;
	wire          rc0_reconfn, rc1_reconfn, rc2_reconfn, rc3_reconfn;

	/* producer consumer interface */
	wire          pc_0_prdy, rr_0_prdy, rr_0_prdy_rr;
	wire          pc_0_crdy, rr_0_crdy, rr_0_crdy_rr;
	wire          pc_0_cerr, rr_0_cerr, rr_0_cerr_rr;
	wire   [31:0] pc_0_data, rr_0_data, rr_0_data_rr;
	
	/* xbus master interface */
	wire          ma0_req   , ma1_req   , ma2_req   , ma3_req   ;
	wire          xbm0_gnt  , xbm1_gnt  , xbm2_gnt  , xbm3_gnt  ;
	wire          ma0_select, ma1_select, ma2_select, ma3_select;
	wire   [31:0] ma0_addr  , ma1_addr  , ma2_addr  , ma3_addr  ;
	wire   [31:0] ma0_data  , ma1_data  , ma2_data  , ma3_data  ;
	wire          ma0_rnw   , ma1_rnw   , ma2_rnw   , ma3_rnw   ;
	wire   [3:0]  ma0_be    , ma1_be    , ma2_be    , ma3_be    ;
	wire          xbm0_ack  , xbm1_ack  , xbm2_ack  , xbm3_ack  ;
	wire   [31:0] xbm0_data , xbm1_data , xbm2_data , xbm3_data ;

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
		.p_prdy           (pc_0_prdy          ),
		.p_crdy           (rr_0_crdy          ),
		.p_cerr           (rr_0_cerr          ),
		.p_data           (pc_0_data          ),
		
		.c_prdy           (rr_0_prdy          ),
		.c_crdy           (pc_0_crdy          ),
		.c_cerr           (pc_0_cerr          ),
		.c_data           (rr_0_data          ),
		
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

	/* reconfigurable region & its isolation logic */
	my_region region_0 (
		.clk              (rc0_clk            ),
		.rstn             (rc0_rstn           ),
		
		//-- to/from producer consumers----
		.p_prdy           (rr_0_prdy_rr       ),
		.p_crdy           (pc_0_crdy          ),
		.p_cerr           (pc_0_cerr          ),
		.p_data           (rr_0_data_rr       ),
		
		.c_prdy           (pc_0_prdy          ),
		.c_crdy           (rr_0_crdy_rr       ),
		.c_cerr           (rr_0_cerr_rr       ),
		.c_data           (pc_0_data          ),
		
		//-- to/from reconfiguration manager----
		.rc_reqn          (rc0_reqn           ),
		.rc_ackn          (rc0_ackn_rr         )
	);
	
	isolator isol_0 (
		//-- to/from reconfiguration-add-ons----
		.rc_ackn_rr       (rc0_ackn_rr        ),
		.rc_ackn          (rc0_ackn           ),
		//-- to/from producer/consumer ----
		.p_prdy           (rr_0_prdy          ),
		.p_prdy_rr        (rr_0_prdy_rr       ),
		.p_data           (rr_0_data          ),
		.p_data_rr        (rr_0_data_rr       ),
		
		.c_crdy           (rr_0_crdy          ),
		.c_crdy_rr        (rr_0_crdy_rr       ),
		.c_cerr           (rr_0_cerr          ),
		.c_cerr_rr        (rr_0_cerr_rr       ),
		//-- to/from reconfiguration manager----
		.is_reconfn       (rc0_reconfn        )
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
		.ma2_req          (1'b0               ),
		.xbm2_gnt         (/* not-connected */),
		.ma2_select       (1'b0               ),
		.ma2_addr         (32'b0              ),
		.ma2_data         (32'b0              ),
		.ma2_rnw          (1'b0               ),
		.ma2_be           (4'b0               ),
		.xbm2_ack         (/* not-connected */),
		.xbm2_data        (/* not-connected */),
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
	
	`define RM_0_ADDR 32'h100
	`define RM_0_SIZE 16

	`define RM_1_ADDR 32'h200
	`define RM_1_SIZE 16

	`define SBT_HEADER_SIZE 16

	`define ONE_CYCLE_DELAY 10ns
	
	`include "tdpr_quick_start.sv"

endmodule
