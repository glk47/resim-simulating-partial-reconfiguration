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

	`define DMA_WR_RM_0_HEADER 32'h400
	`define DMA_RD_RM_0_HEADER 32'h420
	`define DMA_WR_RM_1_HEADER 32'h440
	`define DMA_RD_RM_1_HEADER 32'h460
	
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
	
	`include "tdpr_demo.sv"
	`include "tdpr_simple.sv"
	`include "tdpr_readback.sv"
	`include "tdpr_isolation.sv"
	`include "tdpr_retry.sv"
	`include "tdpr_random.sv"
	
//-------------------------------------------------------------------
// Assertions: interface protocol checking
//-------------------------------------------------------------------

	// icapi-manager::reconfiguration interface
	//     rc_start, rc_done
	
	property icapi_if_sequence();
		@(posedge clk) disable iff(~rstn)
			$rose(rc_start) |=> (~rc_start & ~rc_done)[*0:$] ##1 (~rc_start & rc_done) ##1 (~rc_start & ~rc_done);
	endproperty
	assert_icapi_if_sequence : assert property (icapi_if_sequence);
	
	// icapi-memory::xbus master interface
	//     ma_req, xbm_gnt, ma_select, xbm_ack
	
	sequence req_ack_sequence (req, ack, ACK_MIN_DELAY);
		@(posedge clk) (req) ##1 (req & ~ack)[*ACK_MIN_DELAY:$] ##1 (req & ack) ##1 (~req & ~ack);
	endsequence
	assert_xbus_arbiter : assert property(@(posedge clk) disable iff(~rstn) $rose(ma3_req) |-> req_ack_sequence (ma3_req, xbm3_gnt,0));
	assert_xbus_master  : assert property(@(posedge clk) disable iff(~rstn) $rose(ma3_select) |-> req_ack_sequence (ma3_select, xbm3_ack,0));
	
	cov_xbus_arbiter_icapi_delayed : cover property(@(posedge clk) req_ack_sequence (ma3_req, xbm3_gnt,16));
	
	// reconfigurable region(s)::producer-consumer interface
	//     prdy, crdy, cerr, data
	
	sequence pc_if_start (prdy, crdy, cerr);
		@(posedge clk) ($rose(prdy) || ((prdy) && $past(crdy | cerr)));
	endsequence
	sequence pc_if_crdy (prdy, crdy, cerr);
	
		// This sequence pattern can be used in a typical ready/accept handshake protocol ... 
		// In particular, the pc_if_crdy sequrnce start from ready being asserted, followed by 
		// 0-18 cycles of ready_not_accept (i.e., waiting for the target), followed by 1 cycle 
		// ready_and_accept (i.e., the data transfer cycle)
		// 
		// N.B. the target-accept signal can be asserted at the same clock cycle of source-ready.
		// According to the systemverilog IEEE standard, capturing 0 cycle of ready_not_accept
		// (i.e., ready_not_accept[*0]) is considerred as an empty sequence. For an empty sequence, 
		// the systemverilog IEEE standard says: 
		// 
		//     (empty ##n seq), where n is greater than 0, is equivalent to (##(n-1) seq).
		// 
		// As a result, "ready_not_accept[*0] ##1 ready_and_accept" is equivalent to asserting
		// ready_and_accept at the current clcok cycle 
		
		@(posedge clk) ((prdy & ~crdy)[*0:16] ##1 (prdy & crdy));
	endsequence
	sequence pc_if_cerr (prdy, crdy, cerr);
		@(posedge clk) ((prdy & ~crdy)[*0:16] ##1 (prdy & cerr));
	endsequence
	
	cov_pc_if_0_ready : cover property (@(posedge clk) pc_if_start(rr_0_prdy, pc_0_crdy, pc_0_cerr) ##0 pc_if_crdy(rr_0_prdy, pc_0_crdy, pc_0_cerr));
	cov_pc_if_1_ready : cover property (@(posedge clk) pc_if_start(pc_0_prdy, rr_0_crdy, rr_0_cerr) ##0 pc_if_crdy(pc_0_prdy, rr_0_crdy, rr_0_cerr));
	cov_pc_if_0_error : cover property (@(posedge clk) pc_if_start(rr_0_prdy, pc_0_crdy, pc_0_cerr) ##0 pc_if_cerr(rr_0_prdy, pc_0_crdy, pc_0_cerr));
	cov_pc_if_1_error : cover property (@(posedge clk) pc_if_start(pc_0_prdy, rr_0_crdy, rr_0_cerr) ##0 pc_if_cerr(pc_0_prdy, rr_0_crdy, rr_0_cerr));
	
	property pc_if_sequence (prdy, crdy, cerr);
		@(posedge clk) disable iff(~rstn)
			pc_if_start(prdy, crdy, cerr) |-> (pc_if_crdy(prdy, crdy, cerr) or pc_if_cerr(prdy, crdy, cerr));
	endproperty
	assert_pc_if_0_sequence : assert property(pc_if_sequence (rr_0_prdy, pc_0_crdy, pc_0_cerr));
	assert_pc_if_1_sequence : assert property(pc_if_sequence (pc_0_prdy, rr_0_crdy, rr_0_cerr));
	
	property pc_if_data_hold (prdy, crdy, cerr, data);
	
		// Data should keep stable whilst producer is ready and consumer is not ready
		// The following two sequences are equivlant: 
		// 
		//    @(posedge clk) disable iff(~rstn) (prdy & (~crdy & ~cerr)) |=> $stable(data);
		//    @(posedge clk) disable iff(~rstn) (prdy & (~crdy & ~cerr)) |=> $past(data,1) === data;
		
		@(posedge clk) disable iff(~rstn) (prdy & (~crdy & ~cerr)) |=> $stable(data);
	endproperty
	assert_pc_if_0_data_hold : assert property(pc_if_data_hold (rr_0_prdy, pc_0_crdy, pc_0_cerr, rr_0_data));
	assert_pc_if_1_data_hold : assert property(pc_if_data_hold (pc_0_prdy, rr_0_crdy, rr_0_cerr, pc_0_data));
	
	// manager-module::reconfiguration-add-on interface
	//     reqn, ackn, rc_rstn, reconfn ---- note, becareful about the reset signals (rc_rstn, not rstn)
	
	property recon_if_sequence (reqn, ackn, rc_rstn, reconfn);
		@(posedge clk) disable iff(~rstn) 
			$rose(~reqn) |-> (~reqn & ackn)[*0:$] ##1 (~reqn & ~ackn) ##1 (~reconfn)[*1:$] ##1 (~rc_rstn)[*4] ##1 rc_rstn;
	endproperty
	assert_recon_if_sequence : assert property(recon_if_sequence (rc0_reqn, rc0_ackn, rc0_rstn, rc0_reconfn));
	
	// isolation::request of communication is isolated
	//    is_reconfn, xxxx 
	
	property isolator_stable(is_reconfn, ack, prdy, data, crdy, cerr);
		@(posedge clk) disable iff(~rstn) 
		
		(~is_reconfn) && ($stable(is_reconfn)) 
		|-> $stable(ack) && $stable(prdy) && $stable(data) && $stable(crdy) && $stable(cerr);
	endproperty
	assert_isolator_stable : assert property (isolator_stable(rc0_reconfn,rc0_ackn,rr_0_prdy,rr_0_data,rr_0_crdy,rr_0_cerr));
	
	cov_isolator_cancel_static : cover property (@(posedge clk) ~rc0_reconfn && pc_0_prdy);
	cov_isolator_cancel_rm : cover property (@(posedge clk) ~rc0_reconfn && rr_0_prdy_rr);
	
endmodule
