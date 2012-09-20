//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: XDRS Demo
//
// Create Date:    12/06/2010
// Design Name:    xbuscore
//
//---------------------------------------------------------------------

`timescale 1ns/1ns

module xbuscore 
(
	input                 clk           ,
	input                 rstn          ,

	//-- to/from xbus master0----
	input                 ma0_req       ,
	output reg            xbm0_gnt      ,
	input                 ma0_select    ,
	input      [31:0]     ma0_addr      ,
	input      [31:0]     ma0_data      ,
	input                 ma0_rnw       ,
	input      [3:0]      ma0_be        ,
	output reg            xbm0_ack      ,
	output reg [31:0]     xbm0_data     ,

	//-- to/from xbus master1----
	input                 ma1_req       ,
	output reg            xbm1_gnt      ,
	input                 ma1_select    ,
	input      [31:0]     ma1_addr      ,
	input      [31:0]     ma1_data      ,
	input                 ma1_rnw       ,
	input      [3:0]      ma1_be        ,
	output reg            xbm1_ack      ,
	output reg [31:0]     xbm1_data     ,

	//-- to/from xbus master2----
	input                 ma2_req       ,
	output reg            xbm2_gnt      ,
	input                 ma2_select    ,
	input      [31:0]     ma2_addr      ,
	input      [31:0]     ma2_data      ,
	input                 ma2_rnw       ,
	input      [3:0]      ma2_be        ,
	output reg            xbm2_ack      ,
	output reg [31:0]     xbm2_data     ,

	//-- to/from xbus master3----
	input                 ma3_req       ,
	output reg            xbm3_gnt      ,
	input                 ma3_select    ,
	input      [31:0]     ma3_addr      ,
	input      [31:0]     ma3_data      ,
	input                 ma3_rnw       ,
	input      [3:0]      ma3_be        ,
	output reg            xbm3_ack      ,
	output reg [31:0]     xbm3_data     ,

	//-- to/from xbus slave----
	output reg            xbs_select    ,
	output reg [31:0]     xbs_addr      ,
	output reg [31:0]     xbs_data      ,
	output reg            xbs_rnw       ,
	output reg [3:0]      xbs_be        ,
	input                 sl_ack        ,
	input      [31:0]     sl_data       
	
);

	`define IDLE  4'h0
	`define ARBIT 4'h1
	`define TXFER 4'h2
		
	reg [3:0] state_c, state_n;
	wire isc_has_request; 
	wire isc_transfering;

	reg [3:0] maid; // current master id
	
//-------------------------------------------------------------------
// Switch/Mux
//-------------------------------------------------------------------

	// current master id
	always @(posedge clk or negedge rstn) begin
		if (~rstn)
			maid <= 4'b0;
		else begin
			if (state_c == `ARBIT) begin
				if (xbm0_gnt == 1'b1) begin maid <= 4'h0; end
				else if (xbm1_gnt == 1'b1) begin maid <= 4'h1; end
				else if (xbm2_gnt == 1'b1) begin maid <= 4'h2; end
				else if (xbm3_gnt == 1'b1) begin maid <= 4'h3; end
				else begin maid <= 4'h0; end
			end
		end
	end
	
	always @(*) begin
		case (maid)
			4'h0: begin
				xbs_select  = ma0_select ;
				xbs_addr    = ma0_addr   ;
				xbs_data    = ma0_data   ;
				xbs_rnw     = ma0_rnw    ;
				xbs_be      = ma0_be     ;
				xbm0_ack    = sl_ack     ;
				xbm0_data   = sl_data    ;
			end
			4'h1: begin
				xbs_select  = ma1_select ;
				xbs_addr    = ma1_addr   ;
				xbs_data    = ma1_data   ;
				xbs_rnw     = ma1_rnw    ;
				xbs_be      = ma1_be     ;
				xbm1_ack    = sl_ack     ;
				xbm1_data   = sl_data    ;
			end
			4'h2: begin
				xbs_select  = ma2_select ;
				xbs_addr    = ma2_addr   ;
				xbs_data    = ma2_data   ;
				xbs_rnw     = ma2_rnw    ;
				xbs_be      = ma2_be     ;
				xbm2_ack    = sl_ack     ;
				xbm2_data   = sl_data    ;
			end
			4'h3: begin
				xbs_select  = ma3_select ;
				xbs_addr    = ma3_addr   ;
				xbs_data    = ma3_data   ;
				xbs_rnw     = ma3_rnw    ;
				xbs_be      = ma3_be     ;
				xbm3_ack    = sl_ack     ;
				xbm3_data   = sl_data    ;
			end
			
			default: begin
				xbs_select  = 1'b0;
				xbs_addr    = 32'b0;
				xbs_data    = 32'b0;
				xbs_rnw     = 1'b0;
				xbs_be      = 4'b0;
				xbm0_ack    = 1'b0;
				xbm0_data   = 32'b0;
				xbm1_ack    = 1'b0;
				xbm1_data   = 32'b0;
				xbm2_ack    = 1'b0;
				xbm2_data   = 32'b0;
				xbm3_ack    = 1'b0;
				xbm3_data   = 32'b0;
			end
		endcase
	end
	
//-------------------------------------------------------------------
// Main FSM 
//-------------------------------------------------------------------

	always @(posedge clk or negedge rstn) begin
		if (~rstn)
			state_c <= `IDLE;
		else
			state_c <= state_n;
	end

	assign isc_has_request = ma0_req || ma1_req || ma2_req || ma3_req;
	assign isc_transfering = xbs_select;
	
	always @(*) begin
		{xbm0_gnt,xbm1_gnt,xbm2_gnt,xbm3_gnt} = {1'b0,1'b0,1'b0,1'b0};

		case (state_c)
			`IDLE: begin state_n = (isc_has_request)? `ARBIT:`IDLE; end
			`ARBIT:begin 
				if (ma0_req == 1'b1) begin xbm0_gnt = 1'b1; end
				else if (ma1_req == 1'b1) begin xbm1_gnt = 1'b1; end
				else if (ma2_req == 1'b1) begin xbm2_gnt = 1'b1; end
				else if (ma3_req == 1'b1) begin xbm3_gnt = 1'b1; end
				else begin end
				state_n = `TXFER;
			end
			`TXFER:begin state_n = (isc_transfering)? `TXFER: (isc_has_request)? `ARBIT:`IDLE; end
			default: begin state_n = `IDLE; end
		endcase
	end
	
	// synthesis translate_off
	reg  [8*20:1] state_ascii;
	always @(*) begin
		if      (state_c==`IDLE)     state_ascii <= "IDLE";
		else if (state_c==`ARBIT)    state_ascii <= "ARBIT";
		else if (state_c==`TXFER)    state_ascii <= "TXFER";
		else                         state_ascii <= "ERROR";
	end
	// synthesis translate_on
	
endmodule
