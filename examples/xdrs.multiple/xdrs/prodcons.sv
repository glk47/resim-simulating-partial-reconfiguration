//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: XDRS Demo
//
// Create Date:    12/06/2010
// Design Name:    prodcons
//
//---------------------------------------------------------------------

`timescale 1ns/1ps

import ovm_pkg::*;
`include "ovm_macros.svh"

module prodcons
#(parameter
	C_RETRY_DELAY = 32
)
(
	input                 clk           ,
	input                 rstn          ,

	//-- producer/consumer thread----
	output reg            p_prdy        ,
	input                 p_crdy        ,
	input                 p_cerr        ,
	output reg [31:0]     p_data        ,

	input                 c_prdy        ,
	output reg            c_crdy        ,
	output reg            c_cerr        ,
	input      [31:0]     c_data        ,

	//-- dummy memory traffic thread (xbus master interface)----
	output reg            ma_req        ,
	input                 xbm_gnt       ,
	output reg            ma_select     ,
	output reg [31:0]     ma_addr       ,
	output reg [31:0]     ma_data       ,
	output reg            ma_rnw        ,
	output reg [3:0]      ma_be         ,
	input                 xbm_ack       ,
	input      [31:0]     xbm_data

);

	reg [31:0] p_cnt;
	reg [31:0] c_cnt;

	initial begin
		p_prdy      = 1'b0;
		p_data      = 32'b0;
		c_crdy      = 1'b0;
		c_cerr      = 1'b0;

		ma_req      = 1'b0;
		ma_select   = 1'b0;
		ma_addr     = 32'b0;
		ma_data     = 32'b0;
		ma_rnw      = 1'b0;
		ma_be       = 4'b0;

	end

	initial begin
		p_cnt  <= 32'h0;
		c_cnt  <= 32'h0;
	end

//-------------------------------------------------------------------
// Tasks
//-------------------------------------------------------------------

	task produce_data(input [31:0] d);

		while (1) begin

			/* produce data */
			@(posedge clk); p_prdy  = 1'b1; p_data  = d;

			/* wait and check response */
			@(posedge clk iff ((p_crdy == 1'b1) || (p_cerr == 1'b1))); p_prdy  = 1'b0; p_data  = 0; 
			if (p_crdy == 1'b1) begin break; end
			if (p_cerr == 1'b1) begin repeat(C_RETRY_DELAY) @(posedge clk); continue; end

		end

		p_cnt <= p_cnt + 1;
		ovm_top.ovm_report_info("PRODUCER", $psprintf("Producing the %0dth data: 0x%08h",p_cnt,d), OVM_HIGH);

	endtask : produce_data
	
	task consume_data(output [31:0] d, input bit retry=0);

		/* wait and consume data */
		@(posedge clk); c_crdy = 1'b0; c_cerr = 1'b0;
		
		repeat(retry) begin /* respond with error signal */
			@(posedge clk iff (c_prdy == 1'b1)); repeat ($urandom()%8) @(posedge clk); c_cerr = 1'b1;
			@(posedge clk); c_crdy = 1'b0; c_cerr = 1'b0;
		end
		
		/* respond with ready signal */
		@(posedge clk iff (c_prdy == 1'b1)); repeat ($urandom()%8) @(posedge clk); c_crdy = 1'b1;
		@(posedge clk); c_crdy = 1'b0; c_cerr = 1'b0; d = c_data; 
		
		c_cnt <= c_cnt + 1;
		ovm_top.ovm_report_info("CONSUMER", $psprintf("Consuming the %0dth data: 0x%08h",c_cnt,d), OVM_HIGH);
		
	endtask : consume_data

	task consume_data_nodelay(output [31:0] d);

		/* consume data immediately */
		c_crdy = 1'b1; c_cerr = 1'b0;
		@(posedge clk iff (c_prdy == 1'b1)); d = c_data; 
		
		c_cnt <= c_cnt + 1;
		ovm_top.ovm_report_info("CONSUMER", $psprintf("Consuming the %0dth data: 0x%08h",c_cnt,d), OVM_HIGH);
		
	endtask : consume_data_nodelay
	
	task read_data(input [31:0] a, output [31:0] d);

		@(posedge clk);
		ma_req      = 1'b1;

		@(posedge clk iff (xbm_gnt == 1'b1) );
		ma_req      = 1'b0;
		ma_select   = 1'b1;
		ma_addr     = a;
		ma_rnw      = 1'b1;
		ma_be       = 4'hf;

		@(posedge clk iff (xbm_ack == 1'b1) );
		d           = xbm_data;
		ma_select   = 1'b0;
		ma_addr     = 32'b0;
		ma_rnw      = 1'b0;
		ma_be       = 4'b0;

		ovm_top.ovm_report_info("MEMORYTRAFFIC", $psprintf("Reading data @ 0x%0h : 0x%08h",a,d), OVM_HIGH);

	endtask : read_data

	task write_data(input [31:0] a, input [31:0] d);

		@(posedge clk);
		ma_req      = 1'b1;

		@(posedge clk iff (xbm_gnt == 1'b1) );
		ma_req      = 1'b0;
		ma_select   = 1'b1;
		ma_addr     = a;
		ma_data     = d;
		ma_rnw      = 1'b0;
		ma_be       = 4'hf;

		@(posedge clk iff (xbm_ack == 1'b1) );
		ma_select   = 1'b0;
		ma_addr     = 32'b0;
		ma_data     = 32'b0;
		ma_rnw      = 1'b0;
		ma_be       = 4'b0;

		ovm_top.ovm_report_info("MEMORYTRAFFIC", $psprintf("Writing data @ 0x%0h : 0x%08h",a,d), OVM_HIGH);

	endtask : write_data

endmodule
