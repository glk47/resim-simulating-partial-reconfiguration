/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XPCIe

 Create Date:    15/07/2011
 Design Name:    math_core_adder

 *******************************************************************/

`timescale 1ns/1ps

module math_core
(
	input                     clk      ,
	input                     rst      ,
	input      [0:31]         ain      , // For Reconfigurable Modules, because RMs are 
	input      [0:31]         bin      , // synthesized separately, the IO should match with
	output     [0:31]         result   , // its instantiation in the upper-level 
	output     [0:31]         statistic  // So I must declare them as [0:31] 
);

	adder rm (
		.clk              (  clk              ),
		.rst              (  rst              ),
		.ain              (  ain              ),
		.bin              (  bin              ),
		.result           (  result           ),
		.statistic        (  statistic        )
	);

endmodule
