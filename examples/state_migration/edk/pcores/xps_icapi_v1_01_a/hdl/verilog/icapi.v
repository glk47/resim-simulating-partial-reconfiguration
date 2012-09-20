//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: State_Migration
//
// Create Date:    12/06/2010
// Design Name:    icapi
//
//---------------------------------------------------------------------

`timescale 1ns/1ns
(* KEEP_HIERARCHY = "TRUE" *)
module icapi # (
	parameter C_RESIM           = 1,
	parameter C_FAMILY          = "virtex5",
	parameter C_DWIDTH          = 32 // WAR: !!!! icapi only support 32bit native data width !!!!
)
(
	input                       clk           ,
	input                       rstn          ,

	//-- to/from reconfiguration manager----
	input                       rc_start      /* synthesis syn_keep=1 */,
	input                       rc_bop        /* synthesis syn_keep=1 */,
	input      [31:0]           rc_baddr      /* synthesis syn_keep=1 */,
	input      [31:0]           rc_bsize      /* synthesis syn_keep=1 */,
	output reg                  rc_done       /* synthesis syn_keep=1 */,

	//-- to/from xbus (xbus master interface)----
	output reg                  ma_req        /* synthesis syn_keep=1 */,
	input                       xbm_gnt       /* synthesis syn_keep=1 */,
	output reg                  ma_select     /* synthesis syn_keep=1 */,
	output     [31:0]           ma_addr       /* synthesis syn_keep=1 */,
	output     [C_DWIDTH-1:0]   ma_data       /* synthesis syn_keep=1 */,
	output reg                  ma_rnw        /* synthesis syn_keep=1 */,
	output     [C_DWIDTH/8-1:0] ma_be         /* synthesis syn_keep=1 */,
	input                       xbm_ack       /* synthesis syn_keep=1 */,
	input      [C_DWIDTH-1:0]   xbm_data      /* synthesis syn_keep=1 */

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
	assign cfg_wen = ~((state_c == `WRCFG));
	
	icap_wrapper #(
		.C_RESIM                (C_RESIM            ),
		.C_FAMILY               (C_FAMILY           )
	) icap_0 (                  
		.Icap_clk               (clk                ),
		.Icap_ce                (cfg_cen            ),
		.Icap_we                (cfg_wen            ),
		.Icap_datain            (cfg_data           ),
		.Icap_dataout           (cfg_rdbk_i         ),
		.Icap_busy              (cfg_busy           ) /* Only used for readback */
	);

//-------------------------------------------------------------------
// Assertions & Coverage
//-------------------------------------------------------------------
	
	// synthesis translate_off
	property icapi_wr_cdata(TIME_OUT_CYCLE);
		logic [31:0] cdata; /* the cdata transferred */
		
		@(posedge clk) disable iff(~rstn) 
		
		// Property for writing cdata: 
		//     1. read cdata from xbus
		//     2. cdata is written to icap in TIME_OUT_CYCLE cycles 
		//
		// However, the property doesn't force the order of write. In other words,
		// it allows writing to icap in an out-of-order manner, as long as the 
		// cdata is written to icap within TIME_OUT_CYCLE cycles.
		
		(ma_select && ma_rnw && xbm_ack, cdata=xbm_data) 
		|-> ##[1:TIME_OUT_CYCLE] (~cfg_cen && ~cfg_wen && (cdata==cfg_data)); 
		
		// For a stronger property: 
		//     1. read cdata from xbus
		//     2. in TIME_OUT_CYCLE cycles, a write operation should occur
		//     3. the data written should be cdata
		// 
		//     (ma_select && ma_rnw && xbm_ack, cdata=xbm_data) /* read cdata from xbus */
		//     |-> first_match (##[1:TIME_OUT_CYCLE] (~cfg_cen && ~cfg_wen)) /* an icap write operation */
		//     |-> (cdata==cfg_data); /* the data written to icap */
		// 
		// This property force that the first write operation after reading the xbus
		// should be writting the cdata. it does not allow writing any other data to 
		// be written to the icap in between. However, this property can not be used 
		// in pipelined data transfer. 
		
	endproperty
	assert_icapi_wr_cdata : assert property (icapi_wr_cdata(16));

	property icapi_rd_cdata(TIME_OUT_CYCLE);
		logic [31:0] cdata; /* the cdata transferred */
		
		@(posedge clk) disable iff(~rstn)
		
		// Property for reading cdata: 
		//     1. request to read cdata when not busy
		//     2. in 1 cycles, icap return cdata
		//     2. in TIME_OUT_CYCLE cycles, cdata is written to xbus
		// 
		// However, the property doesn't force the order of read. Please see 
		// "assert_icapi_wr_cdata" for detailed discussion
		
		(~cfg_cen && cfg_wen && ~cfg_busy) |-> 
		##1 (1,cdata=cfg_rdbk_i) 
		##[1:TIME_OUT_CYCLE] (ma_select && ~ma_rnw && xbm_ack && (cdata==ma_data));
		
	endproperty
	assert_icapi_rd_cdata : assert property (icapi_rd_cdata(32));
	
	property icapi_baddr_bsize;
	
		@(posedge clk) disable iff(~rstn)
		
		// Property for incrementing/decrementing address and size: 
		//     1. at the last cycle of a transfer operation 
		//         For wcfg, last cycle = end of WRITE_CFG
		//         For rcfg, last cycle = end of WRITE_MEMORY
		//     2. one-cycle later, baddr++, bsize--
		
		(~cfg_cen && ~cfg_wen) || (ma_select && ~ma_rnw && xbm_ack) 
		|=> (baddr == $past(baddr+1)) && (bsize == $past(bsize-1));
		
	endproperty
	assert_icapi_baddr_bsize : assert property (icapi_baddr_bsize);
	
	property icapi_cdata_start;
		@(posedge clk) disable iff(~rstn)
		
		// Property for ensuring all cdata have been transferred: 
		//     1. upon rc_start, check "baddr/bsize is updated"
		
		(rc_start) |=> (bsize==$past(rc_bsize) && baddr==$past(rc_baddr));
		
	endproperty
	assert_icapi_cdata_start : assert property (icapi_cdata_start);
	
	property icapi_cdata_done;
		@(posedge clk) disable iff(~rstn)
		
		// Property for ensuring all cdata have been transferred: 
		//     1. upon rc_done, check "bsize == 0"
		//
		// As bsize decrements everytime cdata is transferred (assert_icapi_baddr_bsize),
		// bsize==0 implies that all data is transferred
		
		(rc_done) |-> (bsize=='b0);
		
	endproperty
	assert_icapi_cdata_done : assert property (icapi_cdata_done);
	
	covergroup cvg_icapi_mode @rc_start;
		
		// Coverage group for ICAPI operation mode:
		// i.e., read cfg & write cfg
	
		mode: coverpoint rc_bop iff (rc_start==1) {
			bins cur[] = {[0:1]};
			illegal_bins other = default;
		}
		mode_transition: coverpoint rc_bop iff (rc_start==1) {
			bins trans[] = ([0:1] => [0:1]);
			ignore_bins rcfg_after_rcfg = (0=>0);
			illegal_bins other = default;
		}
	endgroup
	
	cvg_icapi_mode cvg_0 = new;
	// synthesis translate_on
	
endmodule
