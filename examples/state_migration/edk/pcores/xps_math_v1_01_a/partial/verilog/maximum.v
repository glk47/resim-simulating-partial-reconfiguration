/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XPCIe

 Create Date:    15/07/2011
 Design Name:    maximum

 *******************************************************************/

`timescale 1ns/1ns

module maximum
(
	input                     clk      ,
	input                     rst      ,
	input      [31:0]         ain      ,
	input      [31:0]         bin      ,
	output reg [31:0]         result   ,
	output reg [31:0]         statistic 
);

//-------------------------------------------------------------------
// Signal Declaration
//-------------------------------------------------------------------

	reg [31:0] result_last;

//-------------------------------------------------------------------
// Main Computation
//-------------------------------------------------------------------

	/* the result & result_last register */
	always @(posedge clk or posedge rst) begin
		if (rst) begin
			result      <= 32'h0;
			result_last <= 32'h0;
		end else begin
			result      <= (ain > bin)? ain: bin;
			result_last <= result;
		end
	end
	
	/* the statistic register */
	always @(posedge clk or posedge rst) begin
		if (rst) begin
			statistic[31:16] <= 16'hf00d;
			statistic[15:0]  <= 16'h0;
		end else begin
			if ( result != result_last ) begin
				statistic[15:0] <= statistic[15:0] + 16'h1;
			end
		end
	end

endmodule





