//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: XDRS Demo
//
// Create Date:    12/06/2010
// Design Name:    manager
//
//---------------------------------------------------------------------

`timescale 1ns/1ps

import ovm_pkg::*;
`include "ovm_macros.svh"

module manager 
(
	input                 clk           ,
	input                 rstn          ,

	//-- reconfiguration manager thread (icapi interface)----
	output reg            rc_start      ,
	output reg            rc_bop        ,
	output reg [31:0]     rc_baddr      ,
	output reg [31:0]     rc_bsize      ,
	input                 rc_done       ,
	
	//-- reconfiguration manager thread (reconfiguration-add-on interface)----
	output reg            rc0_reqn      ,
	input                 rc0_ackn      ,
	output                rc0_clk       ,
	output reg            rc0_rstn      ,
	output reg            rc0_reconfn   ,
	output reg            rc1_reqn      ,
	input                 rc1_ackn      ,
	output                rc1_clk       ,
	output reg            rc1_rstn      ,
	output reg            rc1_reconfn   ,
	output reg            rc2_reqn      ,
	input                 rc2_ackn      ,
	output                rc2_clk       ,
	output reg            rc2_rstn      ,
	output reg            rc2_reconfn   ,
	output reg            rc3_reqn      ,
	input                 rc3_ackn      ,
	output                rc3_clk       ,
	output reg            rc3_rstn      ,
	output reg            rc3_reconfn   

);

	logic [3:0] rrid;
	logic [3:0] rmid;
	logic rc_rstn_i, rc_reqn_i, rc_ackn_i,rc_reconfn_i;
	
	logic [3:0] rc_clk_en;
	
	initial begin
		rc_clk_en = 4'hf;
		rrid = 4'h0;
		rmid = 4'h0;
		
		rc_start  = 1'b0;
		rc_bop    = 1'h0;
		rc_baddr  = 32'hffff_ffff;
		rc_bsize  = 32'hffff_ffff;
		
		rc_reqn_i = 1'b1;
		rc_reconfn_i = 1'b1;
		
		rc_rstn_i <= 1'b0; 
		for (int i=0; i < 16; i++ ) begin
			rrid = i; repeat (4) @(posedge clk);
		end
		rc_rstn_i <= 1'b1;
		
		rrid = 4'hf;
		rmid = 4'hf;
	end
	
//-------------------------------------------------------------------
// Muxing req/ack/rst/reconfn
//-------------------------------------------------------------------
	
	always @(*) begin
		rc0_rstn = 1'b1; rc1_rstn = 1'b1; rc2_rstn = 1'b1; rc3_rstn = 1'b1;
		case (rrid)
			4'h0: begin rc0_rstn = rc_rstn_i ; end
			4'h1: begin rc1_rstn = rc_rstn_i ; end
			4'h2: begin rc2_rstn = rc_rstn_i ; end
			4'h3: begin rc3_rstn = rc_rstn_i ; end
			default: begin end
		endcase
	end
	
	always @(*) begin
		rc0_reqn = 1'b1; rc1_reqn = 1'b1; rc2_reqn = 1'b1; rc3_reqn = 1'b1;
		case (rrid)
			4'h0: begin rc0_reqn = rc_reqn_i; end
			4'h1: begin rc1_reqn = rc_reqn_i; end
			4'h2: begin rc2_reqn = rc_reqn_i; end
			4'h3: begin rc3_reqn = rc_reqn_i; end
			default: begin end
		endcase
	end
	
	always @(*) begin
		rc_ackn_i= 1'b1;
		case (rrid)
			4'h0: begin rc_ackn_i = rc0_ackn; end
			4'h1: begin rc_ackn_i = rc1_ackn; end
			4'h2: begin rc_ackn_i = rc2_ackn; end
			4'h3: begin rc_ackn_i = rc3_ackn; end
			default: begin end
		endcase
	end
	
	always @(*) begin
		rc0_reconfn = 1'b1; rc1_reconfn = 1'b1; rc2_reconfn = 1'b1; rc3_reconfn = 1'b1;
		case (rrid)
			4'h0: begin rc0_reconfn = rc_reconfn_i ; end
			4'h1: begin rc1_reconfn = rc_reconfn_i ; end
			4'h2: begin rc2_reconfn = rc_reconfn_i ; end
			4'h3: begin rc3_reconfn = rc_reconfn_i ; end
			default: begin end
		endcase
	end
	
	assign rc0_clk = rc_clk_en[0] & clk;
	assign rc1_clk = rc_clk_en[1] & clk;
	assign rc2_clk = rc_clk_en[2] & clk;
	assign rc3_clk = rc_clk_en[3] & clk;
	
//-------------------------------------------------------------------
// Tasks
//-------------------------------------------------------------------

	task reconfigure_module(input [8:0] cfg, input [31:0] a, input [31:0] s);
		
		rrid = cfg[7:4];
		rmid = cfg[3:0];
		
		/* BEFORE Recon.: unload module */
		@(posedge clk);
		ovm_top.ovm_report_info("MANAGER", $psprintf("Reconfigure module: rrid:%0d rmid:%0d",rrid,rmid), OVM_MEDIUM);
		
		rc_reqn_i = 1'b0;
		@(posedge clk iff (rc_ackn_i == 0)); rc_reqn_i = 1'b1; rc_reconfn_i = 1'b0;
		
		/* DURING Recon.: transfer bitstream */
		@(posedge clk);
		rc_start = 1'b1;
		rc_bop = 1'b1;
		rc_baddr = a;
		rc_bsize = s;
		
		@(posedge clk);
		rc_start = 1'b0;

		@(posedge clk iff (rc_done == 1'b1) );
		rc_reconfn_i = 1'b1; 
		
		/* AFTER Recon.: reset module */
		rc_rstn_i = 1'b0; repeat (4) @(posedge clk); rc_rstn_i <= 1'b1; 
		ovm_top.ovm_report_info("MANAGER", "Reconfiguration DONE", OVM_MEDIUM);

		rrid = 4'hf;
		rmid = 4'hf;
		
	endtask : reconfigure_module

	task icap_dma_bitstream(input op, input [31:0] a, input [31:0] s);
		
		@(posedge clk);
		rc_start = 1'b1;
		rc_bop = op;
		rc_baddr = a;
		rc_bsize = s;
		
		@(posedge clk);
		rc_start = 1'b0;
		if (op == 1'b0)
			ovm_top.ovm_report_info("MANAGER", $psprintf("Read ICAP (DMA): a:0x%0x s:0x%0x",a,s), OVM_MEDIUM);
		else
			ovm_top.ovm_report_info("MANAGER", $psprintf("Write ICAP (DMA): a:0x%0x s:0x%0x",a,s), OVM_MEDIUM);

		@(posedge clk iff (rc_done == 1'b1) );
		ovm_top.ovm_report_info("MANAGER", "Read/Write ICAP DONE", OVM_MEDIUM);

	endtask : icap_dma_bitstream
	
	task set_rc_clock_en(input [3:0] en);
		rc_clk_en = en;
	endtask : set_rc_clock_en
	
endmodule
