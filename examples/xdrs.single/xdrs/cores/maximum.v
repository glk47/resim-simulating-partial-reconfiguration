/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XDRS

 Create Date:    19/09/2010
 Design Name:    maximum

 *******************************************************************/

`timescale 1ns/1ns

module maximum
#(parameter
	C_CNT_BW = 32,
	C_RETRY_DELAY = 16
)
(
	input                 clk           ,
	input                 rstn          ,

	//-- to/from producer/consumer ----
	output                p_prdy        ,
	input                 p_crdy        ,
	input                 p_cerr        ,
	output     [31:0]     p_data        ,

	input                 c_prdy        ,
	output                c_crdy        ,
	output                c_cerr        ,
	input      [31:0]     c_data        ,
	
	//-- to/from reconfiguration controller----
	input                 rc_reqn       ,
	output                rc_ackn       
);

//-------------------------------------------------------------------
// Signal Declaration
//-------------------------------------------------------------------

	/* main data register: data1,2 */
	wire data1_wr_en, data2_wr_en;
	wire is_data_1; wire is_data_2;
	reg [31:0] data1,data2;

	/* retry & timeout counter */
	reg [7:0] retrycnt; wire is_retry;
	reg [3:0] tocnt;
	
	/* main fsm */
	reg [3:0] state_c, state_n;

	localparam [3:0]
		S_Rd1      = 4'd0,
		S_Rd2      = 4'd1,
		S_Wr       = 4'd2,
		S_ReTry    = 4'd3,
		S_IDLE     = 4'd15;
	
//-------------------------------------------------------------------
// Datapath Registers
//-------------------------------------------------------------------

	/* the retry & timeout counter */
	always @(posedge clk or negedge rstn) begin
		if (~rstn) begin
			retrycnt <= 8'h0;
		end else begin
			if (state_c == S_ReTry) retrycnt <= retrycnt+1'b1;
			else if (state_c == S_Wr) retrycnt <= 'b0;
		end
	end
	assign is_retry = (retrycnt == C_RETRY_DELAY-1);
	
	always @(posedge clk or negedge rstn) begin
		if (~rstn) begin
			tocnt <= 4'h0;
		end else begin
			if (c_prdy && ~c_crdy) tocnt <= tocnt + 'h1;
			else tocnt <= 4'h0;
		end
	end
	assign c_cerr = (tocnt == 4'hf) & (~c_crdy);
	
	/* the data1,2 register */
	assign data1_wr_en = c_prdy & c_crdy & is_data_1;
	assign data2_wr_en = c_prdy & c_crdy & is_data_2;
	always @(posedge clk or negedge rstn) begin
		if (~rstn) begin
			data1 <= 32'h0;
			data2 <= 32'h0;
		end else begin
			if (data1_wr_en) data1 <= c_data;
			if (data2_wr_en) data2 <= c_data;
		end
	end

	/* assigning the output signals */
	assign p_data = (data1 > data2)? data1: data2;

	/* instantiate the stastical counter */
	stat_cnt #(C_CNT_BW) stat_0(
		.clk(clk),
		.rstn(rstn),
		//-- to/from the datapath to be monitored----
		.din(c_data),
		.din_valid(c_prdy & c_crdy),
		.dout(p_data),
		.dout_valid(p_prdy & p_crdy)
	);
	
//-------------------------------------------------------------------
// Main FSM - Maximum fsm
//-------------------------------------------------------------------

	always @(posedge clk or negedge rstn) begin
		if (~rstn)
			state_c <= S_IDLE;
		else
			state_c <= state_n;
	end
	
	always @(*) begin
		case (state_c)
			S_IDLE:begin state_n = (c_prdy)? S_Rd1:S_IDLE; end
			S_Rd1:begin state_n = (c_prdy)? S_Rd2:S_Rd1; end
			S_Rd2:begin state_n = (c_prdy)? S_Wr:S_Rd2; end 
			S_Wr: begin state_n = (p_crdy)? S_IDLE: (p_cerr)? S_ReTry:S_Wr; end
			S_ReTry: begin state_n = (is_retry)? S_Wr: S_ReTry; end
			
			default: begin state_n = S_IDLE; end
		endcase
	end

	assign p_prdy = (state_c == S_Wr);
	assign c_crdy = (state_c == S_Rd1) || (state_c == S_Rd2);
	assign is_data_1 = (state_c == S_Rd1);
	assign is_data_2 = (state_c == S_Rd2);

	// synthesis translate_off
	reg  [8*20:1] state_ascii;
	always @(*) begin
		if      (state_c==S_Rd1)     state_ascii <= "RD1";
		else if (state_c==S_Rd2)     state_ascii <= "RD2";
		else if (state_c==S_Wr)      state_ascii <= "WR";
		else if (state_c==S_ReTry)   state_ascii <= "RETRY";
		else if (state_c==S_IDLE)    state_ascii <= "IDLE";
		else                         state_ascii <= "ERROR";
	end
	// synthesis translate_on

//-------------------------------------------------------------------
// InternSync
//-------------------------------------------------------------------

	/* intern_sync: synchronize by monitoring the internal idle signal */
	wire rc_is_idle;
	assign rc_is_idle = (state_c == S_IDLE);

	/* instantiate the reconfiguration add-on: intern_sync */
	intern_sync sync_0(
		.clk(clk),
		.rstn(rstn),
		//-- to/from core----
		.rc_is_idle(rc_is_idle),
		//-- to/from reconfiguration controller----
		.rc_reqn(rc_reqn),
		.rc_ackn(rc_ackn)
	);

//-------------------------------------------------------------------
// Assertions & Coverage
//-------------------------------------------------------------------

	// synthesis translate_off
	property maximum_operation;
		logic [31:0] d1,d2;
		
		@(posedge clk) disable iff(~rstn)
		
		// Property for maximum operation: 
		//     1. start of operation: ((state_n == S_IDLE) && c_prdy)
		//     2. read 2 data and write out the larger one
		
		((state_c == S_IDLE) && c_prdy) |->
		##[1:$] (c_prdy && c_crdy,d1=c_data) ##[1:$] (c_prdy && c_crdy,d2=c_data) 
		##[1:$] (p_prdy && p_crdy && (p_data==(d1>d2?d1:d2)));
		
	endproperty
	assert_maximum_operation : assert property (maximum_operation);

	covergroup cvg_maximum_oprand @(p_prdy & p_crdy);
		range: coverpoint p_data {
			bins gt = {[0:'1]} iff(data1>data2);
			bins eq = {[0:'1]} iff(data1==data2);
			bins lt = {[0:'1]} iff(data1<data2);
		}
	endgroup
	cvg_maximum_oprand cvg_0 = new;
	
	covergroup cvg_maximum_cfg_req @(posedge clk);
	
		// When the request of reconfiguration is detected
		// probe the fsm. Should test reconfiguration at each fsm state
	
		cfg: coverpoint state_c iff (~rc_reqn) {
			bins cfg[] = {S_Rd1,S_Rd2,S_Wr,S_ReTry,S_IDLE};
			illegal_bins other = default;
		}
	endgroup
	cvg_maximum_cfg_req cvg_1 = new;
	
	assert_maximum_cfg_ack : assert property (@(posedge clk) disable iff(~rstn)
	
		// Reconfiguration can only be acknowledged when IDLE
		// by using the intern_sync, the maximum module can only be reconfigured 
		// at S_IDLE state
		// 
		// The corner case is acknowledge and start computation 
		// at the same time, and "un-intended" computation should be isolated correctly
		
		(~rc_ackn) |-> (state_c == S_IDLE)
	);
	cov_maximum_cfg_ack : cover property (@(posedge clk) $fell(rc_ackn) |-> ((state_c==S_IDLE) ##1 (state_c!=S_IDLE)));
	
	// Reset property:
	// when reset, internal signals should go to default values (to test just a few)
	
	cov_maximum_reset_0 : cover property (@(posedge clk) (~rstn) |-> (($past(state_c) !== S_IDLE) ##0 (state_c === S_IDLE)));
	cov_maximum_reset_1 : cover property (@(posedge clk) (~rstn) |-> (($past(data1) !== 'h0) ##0 (data1 === 'h0)));
	cov_maximum_reset_2 : cover property (@(posedge clk) (~rstn) |-> (($past(data2) !== 'h0) ##0 (data2 === 'h0)));
	
	// Corner case: 
	// drive ready or error at the last cycle of time out
	
	cov_maximum_crdy : cover property (@(posedge clk) (tocnt == 4'hf) |-> c_crdy );
	cov_maximum_cerr : cover property (@(posedge clk) (tocnt == 4'hf) |-> c_cerr );
	// synthesis translate_on
	
endmodule





