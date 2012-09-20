/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XDRS

 Create Date:    19/09/2010
 Design Name:    reverse

 *******************************************************************/

`timescale 1ns/1ns

module reverse
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
	wire is_data_1; wire is_data_2; wire is_1_or_2;
	reg [31:0] data1,data2;

	/* retry & timeout counter */
	reg [7:0] retrycnt; wire is_retry;
	reg [3:0] tocnt;
	
	/* main fsm */
	reg [3:0] state_c, state_n;

	localparam [3:0]
		S_Rd1      = 4'd0,
		S_Rd2      = 4'd1,
		S_Wr1      = 4'd2,
		S_Wr2      = 4'd3,
		S_ReTry1   = 4'd4,
		S_ReTry2   = 4'd5,
		S_IDLE     = 4'd15;

//-------------------------------------------------------------------
// Datapath Registers
//-------------------------------------------------------------------

	/* the retry & timeout counter */
	always @(posedge clk or negedge rstn) begin
		if (~rstn) begin
			retrycnt <= 8'h0;
		end else begin
			if ((state_c == S_ReTry1)||(state_c == S_ReTry2)) retrycnt <= retrycnt+1'b1;
			else if ((state_c == S_Wr1)||(state_c == S_Wr2)) retrycnt <= 'b0;
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
	assign p_data = (is_1_or_2)? data2: data1;

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
// Main FSM - Reverse fsm
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
			S_Rd2:begin state_n = (c_prdy)? S_Wr1:S_Rd2; end 
			S_Wr1:begin state_n = (p_crdy)? S_Wr2: (p_cerr)? S_ReTry1: S_Wr1; end
			S_Wr2:begin state_n = (p_crdy)? S_IDLE: (p_cerr)? S_ReTry2: S_Wr2; end
			S_ReTry1: begin state_n = (is_retry)? S_Wr1: S_ReTry1; end
			S_ReTry2: begin state_n = (is_retry)? S_Wr2: S_ReTry2; end
			
			default: begin state_n = S_IDLE; end
		endcase
	end

	assign p_prdy = (state_c == S_Wr1) || (state_c == S_Wr2);
	assign c_crdy = (state_c == S_Rd1) || (state_c == S_Rd2);
	assign is_data_1 = (state_c == S_Rd1);
	assign is_data_2 = (state_c == S_Rd2);
	assign is_1_or_2 = (state_c == S_Wr1);

	// synthesis translate_off
	reg  [8*20:1] state_ascii;
	always @(*) begin
		if      (state_c==S_Rd1)     state_ascii <= "RD1";
		else if (state_c==S_Rd2)     state_ascii <= "RD2";
		else if (state_c==S_Wr1)     state_ascii <= "WR1";
		else if (state_c==S_Wr2)     state_ascii <= "WR2";
		else if (state_c==S_ReTry1)  state_ascii <= "RETRY1";
		else if (state_c==S_ReTry2)  state_ascii <= "RETRY2";
		else if (state_c==S_IDLE)    state_ascii <= "IDLE";
		else                         state_ascii <= "ERROR";
	end
	// synthesis translate_on
	
//-------------------------------------------------------------------
// FilterSync
//-------------------------------------------------------------------

	/* filter_sync: synchronize by monitoring module IO */
	
	/* instantiate the reconfiguration add-on: filter_sync */
	filter_sync #(32'h1,32'h1) sync_0(
		.clk(clk),
		.rstn(rstn),
		//-- to/from core----
		.is_data_in(c_prdy & c_crdy),
		.is_data_out(p_prdy & p_crdy),
		//-- to/from centeral reconfiguration controller----
		.rc_reqn(rc_reqn),
		.rc_ackn(rc_ackn)
	);

endmodule





