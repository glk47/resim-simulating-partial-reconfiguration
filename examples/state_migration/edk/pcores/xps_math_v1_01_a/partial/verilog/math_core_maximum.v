/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XPCIe

 Create Date:    15/07/2011
 Design Name:    math_core_maximum

 *******************************************************************/

`timescale 1ns/1ps

module math_core
(
	input                     clk      ,
	input                     rst      ,
	input      [0:31]         ain      ,
	input      [0:31]         bin      ,
	output     [0:31]         result   ,
	output     [0:31]         statistic 
);

	maximum rm (
		.clk              (  clk              ),
		.rst              (  rst              ),
		.ain              (  ain              ),
		.bin              (  bin              ),
		.result           (  result           ),
		.statistic        (  statistic        )
	);

endmodule
