/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XSPACE

 Create Date:    17/07/2012
 Design Name:    gfirTF

 *******************************************************************/

`timescale 1ns/1ns

module gfirTF
#(parameter
	C_IWIDTH = 16,
	C_OWIDTH = 32,
	C_CWIDTH = 16,
	C_CLENGTH = 21
)
(
	input                         clk           ,
	input                         sclr          ,

	input                         en            ,
	input  signed [C_IWIDTH-1:0]  din           ,
	output signed [C_OWIDTH-1:0]  dout          

);

//-------------------------------------------------------------------
// Signal Declaration
//-------------------------------------------------------------------
	
	wire signed [C_CWIDTH-1:0] coeff_mem[0:C_CLENGTH-1];
	reg signed [C_IWIDTH-1:0] X_reg[0:C_CLENGTH-1];
	
	wire signed [C_IWIDTH-1:0] X_k;
	
//-------------------------------------------------------------------
// Coefficient Declaration
//-------------------------------------------------------------------
	
	assign coeff_mem[0] = 6;
	assign coeff_mem[1] = 0;
	assign coeff_mem[2] = -4;
	assign coeff_mem[3] = -3;
	assign coeff_mem[4] = 5;
	assign coeff_mem[5] = 6;
	assign coeff_mem[6] = -6;
	assign coeff_mem[7] = -13;
	assign coeff_mem[8] = 7;
	assign coeff_mem[9] = 44;
	
	assign coeff_mem[10] = 64;
	
	assign coeff_mem[11] = 44;
	assign coeff_mem[12] = 7;
	assign coeff_mem[13] = -13;
	assign coeff_mem[14] = -6;
	assign coeff_mem[15] = 6;
	assign coeff_mem[16] = 5;
	assign coeff_mem[17] = -3;
	assign coeff_mem[18] = -4;
	assign coeff_mem[19] = 0;
	assign coeff_mem[20] = 6;
	
//-------------------------------------------------------------------
// Datapath Registers
//-------------------------------------------------------------------
	
	/* datapath: transposed tapped delay lines */
	integer i;
	always @(posedge clk) begin
		if (en==1'b1) begin
			X_reg[0] <= 0 + X_k * coeff_mem[C_CLENGTH-1];
			for (i = 1; i <= C_CLENGTH-1; i = i + 1)
				X_reg[i] <= X_reg[i-1] + X_k * coeff_mem[C_CLENGTH-i-1];
				
		end
	end
	
	assign X_k  = din;
	assign dout = X_reg[C_CLENGTH-1];
	
	// synthesis translate_off
	initial begin
		for (i = 0; i <= C_CLENGTH-1; i = i + 1)
			X_reg[i] <= 'h0;
	end
	// synthesis translate_on
	
endmodule





