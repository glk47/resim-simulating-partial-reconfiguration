//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: XDRS Demo
//
// Create Date:    12/06/2010
// Design Name:    memctrl
//
//---------------------------------------------------------------------

`timescale 1ns/1ps

import ovm_pkg::*;
`include "ovm_macros.svh"

module memctrl 
#(parameter
	MEMDELAY = 1
)
(
	input                 clk           ,
	input                 rstn          ,

	//-- to/from xbus (xbus slave interface)----
	input                 xbs_select    ,
	input      [31:0]     xbs_addr      ,
	input      [31:0]     xbs_data      ,
	input                 xbs_rnw       ,
	input      [3:0]      xbs_be        ,
	output reg            sl_ack        ,
	output reg [31:0]     sl_data       

);

	reg [31:0] zbtmem [0:4095];

	initial begin
		sl_ack = 1'b0;
		sl_data = 32'b0;
		
		forever begin
			logic [31:0] addr;  // address is word address
			logic [3:0]  be;    // byte enable
			
			@(posedge clk iff (xbs_select == 1'b1) );
			addr = xbs_addr[31:0];
			be = xbs_be[3:0];
			
			if (xbs_rnw == 1'b1) begin
				
				sl_data[31:24] = (be[3])? zbtmem[addr][31:24] : 8'b0; // BE memory: MSB = mem[addr][31:24]
				sl_data[23:16] = (be[2])? zbtmem[addr][23:16] : 8'b0;
				sl_data[15:8]  = (be[1])? zbtmem[addr][15:8]  : 8'b0;
				sl_data[7:0]   = (be[0])? zbtmem[addr][7:0]   : 8'b0;
				
				ovm_top.ovm_report_info("MEMORY", $psprintf("Read a:0x%08x be:0x%01x d:0x%08x",addr,be,sl_data),OVM_FULL);
				
			end else if (xbs_rnw == 1'b0) begin
				
				zbtmem[addr][31:24] = (be[3])? xbs_data[31:24] : zbtmem[addr][31:24];
				zbtmem[addr][23:16] = (be[2])? xbs_data[23:16] : zbtmem[addr][23:16];
				zbtmem[addr][15:8]  = (be[1])? xbs_data[15:8]  : zbtmem[addr][15:8] ;
				zbtmem[addr][7:0]   = (be[0])? xbs_data[7:0]   : zbtmem[addr][7:0]  ;
				
				ovm_top.ovm_report_info("MEMORY", $psprintf("Write a:0x%08x be:0x%01x d:0x%08x",addr,be,xbs_data),OVM_FULL);
				
			end else begin
				/* un-defined */
			end
			
			repeat(MEMDELAY) @(posedge clk);
			
			@(posedge clk); sl_ack = 1'b1;
			@(posedge clk); sl_ack = 1'b0;
			
		end
		
	end

endmodule
