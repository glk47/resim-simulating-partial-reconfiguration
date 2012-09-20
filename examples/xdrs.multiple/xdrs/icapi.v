//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: XDRS Demo
//
// Create Date:    12/06/2010
// Design Name:    icapi
//
//---------------------------------------------------------------------

`timescale 1ns/1ns

module icapi 
(
	input                 clk           ,
	input                 rstn          ,

	//-- to/from reconfiguration manager----
	input                 rc_start      ,
	input                 rc_bop        ,
	input      [31:0]     rc_baddr      ,
	input      [31:0]     rc_bsize      ,
	output reg            rc_done       ,

	//-- to/from xbus (xbus master interface)----
	output reg            ma_req        ,
	input                 xbm_gnt       ,
	output reg            ma_select     ,
	output     [31:0]     ma_addr       ,
	output     [31:0]     ma_data       ,
	output reg            ma_rnw        ,
	output     [3:0]      ma_be         ,
	input                 xbm_ack       ,
	input      [31:0]     xbm_data      

);
	
	`define IDLE     8'h0
	`define REQMEM   8'h1
	`define RDMEM    8'h2
	`define WRCFG    8'h3
	`define RDCFG    8'h4
	`define RDLATCH  8'h5
	`define WRMEM    8'h6
	`define DONE     8'h7

	reg [31:0] baddr, bsize;
	reg bop;
	
	wire is_more;
	wire cfg_wen, cfg_cen, cfg_busy;
	wire cfg_data_wr_en, cfg_rdbk_wr_en;
	reg [31:0] cfg_data, cfg_rdbk;
	wire [31:0] cfg_rdbk_i;
	
	reg [7:0] state_c, state_n;
	
//-------------------------------------------------------------------
// bitstream address, size, etc
//-------------------------------------------------------------------

	/* bitstream start_address & size (w.r.t memory) */
	always @(posedge clk or negedge rstn) begin
		if (~rstn) begin
			baddr <= 32'b0;
			bsize <= 32'b0;
			bop <= 1'b0;
		end else begin
			if (rc_start) begin
				baddr <= rc_baddr;
				bsize <= rc_bsize;
				bop <= rc_bop;
			end else if ((state_c == `WRCFG) || ((state_c == `WRMEM)&&(xbm_ack == 1'b1))) begin
				
				// Should update address/size at the last cycle of a transfer 
				// operation. For wcfg, state WRCFG is the last cycle... For rcfg
				// state WRMEM is the last state but it last for more than 
				// one clock cycle, so we need (state_c == `WRMEM)&&(xbm_ack == 1'b1)
				
				baddr <= baddr + 32'h1;
				bsize <= bsize - 32'h1;
			end
		end
	end
	assign is_more = (bsize > 32'h1);
	
//-------------------------------------------------------------------
// Main FSM
//-------------------------------------------------------------------

	always @(posedge clk or negedge rstn) begin
		if (~rstn)
			state_c <= `IDLE;
		else
			state_c <= state_n;
	end
	
	`define DO_REQ begin ma_req = 1'b1; end
	`define DO_RD_MEM begin ma_select = 1'b1; ma_rnw = 1'b1; end
	`define DO_WR_MEM begin ma_select = 1'b1; ma_rnw = 1'b0; end
	
	assign ma_addr = baddr;
	assign ma_data = cfg_rdbk;
	assign ma_be   = 4'hf;
	
	always @(*) begin
		rc_done = 1'b0;
		ma_req = 1'b0; ma_select = 1'b0; ma_rnw = 1'b0;
		
		case (state_c)
			`IDLE: begin state_n = (rc_start)? `REQMEM: `IDLE; end
			`REQMEM: begin state_n = (~xbm_gnt)? `REQMEM: (bop)?`RDMEM:`RDCFG ; `DO_REQ end
			
			// bop == 1'b0: rcfg, icap -> memory
			// RCFG need an additional cycle (`RDLATCH) to latch the cdata_rb into register
			`RDCFG: begin state_n = (cfg_busy)? `RDCFG: `RDLATCH; end
			`RDLATCH: begin state_n = `WRMEM; end
			`WRMEM: begin state_n = (~xbm_ack)? `WRMEM: (is_more)?`REQMEM:`DONE; `DO_WR_MEM end
			
			// bop == 1'b1: wcfg, memory -> icap
			`RDMEM: begin state_n = (~xbm_ack)? `RDMEM:`WRCFG; `DO_RD_MEM end
			`WRCFG: begin state_n = (is_more)? `REQMEM:`DONE; end
			
			`DONE: begin state_n = `IDLE; rc_done = 1'b1; end
			default: begin state_n = `IDLE; end
		endcase
	end
	
	// synthesis translate_off
	reg  [8*20:1] state_ascii;
	always @(*) begin
		if      (state_c==`IDLE)     state_ascii <= "IDLE";
		else if (state_c==`REQMEM)   state_ascii <= "REQMEM";
		else if (state_c==`RDMEM)    state_ascii <= "RDMEM";
		else if (state_c==`WRCFG)    state_ascii <= "WRCFG";
		else if (state_c==`RDCFG)    state_ascii <= "RDCFG";
		else if (state_c==`RDLATCH)  state_ascii <= "RDLATCH";
		else if (state_c==`WRMEM)    state_ascii <= "WRMEM";
		else if (state_c==`DONE)     state_ascii <= "DONE";
		else                         state_ascii <= "ERROR";
	end
	// synthesis translate_on

//-------------------------------------------------------------------
// ICAP
//-------------------------------------------------------------------
	
	assign cfg_data_wr_en = ((state_c == `RDMEM)&&(xbm_ack == 1'b1));
	always @(posedge clk or negedge rstn) begin
		if (~rstn)
			cfg_data <= 32'b0;
		else
			if (cfg_data_wr_en) cfg_data <= xbm_data;
	end
	
	assign cfg_rdbk_wr_en = (state_c == `RDLATCH);
	always @(posedge clk or negedge rstn) begin
		if (~rstn)
			cfg_rdbk <= 32'b0;
		else
			if (cfg_rdbk_wr_en) cfg_rdbk <= cfg_rdbk_i;
	end
	
	assign cfg_cen = ~((state_c == `WRCFG) || (state_c == `RDCFG));
	assign cfg_wen = ~((state_c != `IDLE) && bop); // WRCFG: bop = 1'b1; RDCFG: bop = 1'b0;
	
	ICAP_VIRTEX4_WRAPPER #("X32") icap_0 (
		.CLK         (clk                ),
		.CE          (cfg_cen            ),
		.WRITE       (cfg_wen            ),
		.I           (cfg_data           ),
		.O           (cfg_rdbk_i         ),
		.BUSY        (cfg_busy           )
	);

endmodule
