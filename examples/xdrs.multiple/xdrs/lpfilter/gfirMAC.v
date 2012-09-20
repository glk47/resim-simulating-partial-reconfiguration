/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XSPACE

 Create Date:    17/07/2012
 Design Name:    gfirMAC

 *******************************************************************/

`timescale 1ns/1ns

module gfirMAC
#(parameter
	C_IWIDTH = 16,
	C_OWIDTH = 32,
	C_CWIDTH = 16,
	C_CLENGTH = 21
)
(
	input                         clk           ,
	input                         sclr          ,

	input                         nd            ,
	output                        rfd           ,
	output                        rdy           ,
	input  signed [C_IWIDTH-1:0]  din           ,
	output signed [C_OWIDTH-1:0]  dout          

);

//-------------------------------------------------------------------
// Signal Declaration
//-------------------------------------------------------------------
	
	wire signed [C_CWIDTH-1:0] coeff_mem[0:C_CLENGTH-1];
	reg signed [C_IWIDTH-1:0] X_reg[0:C_CLENGTH-1];
	reg signed [C_OWIDTH-1:0] partial_product;
	
	wire is_idle, is_end_mac;
	reg [7:0] maccnt;
	
	wire signed [C_IWIDTH-1:0] X_kmi;
	wire signed [C_CWIDTH-1:0] A_i;
	
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
	
	/* control path: mac counter */
	always @(posedge clk) begin
		if (sclr) begin
			maccnt <= 8'hff; // IDLE
		end else begin
			if (is_idle)
				maccnt <= (nd==1'b1)? 8'h0 : 8'hff;
			else if (is_end_mac)
				maccnt <= 8'hff;
			else
				maccnt <= maccnt+1'b1;
		end
	end
	assign is_idle    = (maccnt == 8'hff);
	assign is_end_mac = (maccnt == C_CLENGTH);
	
	assign rfd = is_idle;
	assign rdy = is_end_mac;
	
	/* datapath: partial product */
	always @(posedge clk) begin
		if (is_idle)
			partial_product <= {C_OWIDTH{1'b0}};
		else 
			partial_product <= X_kmi * A_i + partial_product;
	end
	assign X_kmi = (maccnt < C_CLENGTH)? X_reg[maccnt] : 'h0;
	assign A_i   = (maccnt < C_CLENGTH)? coeff_mem[maccnt] : 'h0;
	
	assign dout  = partial_product;
	
	/* datapath: delay lines .OR. shif registers */
	integer i;
	always @(posedge clk) begin
		if ((is_idle) && (nd==1'b1)) begin
			X_reg[0] <= din;
			for (i = 1; i <= C_CLENGTH-1; i = i + 1)
				X_reg[i] <= X_reg[i-1];
				
		end
	end
	
	// synthesis translate_off
	initial begin
		for (i = 0; i <= C_CLENGTH-1; i = i + 1)
			X_reg[i] <= 'h0;
	end
	// synthesis translate_on

	// synthesis translate_off
	reg  [8*20:1] state_ascii;
	always @(*) begin
		if      (maccnt==8'hff)      state_ascii <= "IDLE";
		else if (maccnt<C_CLENGTH)   state_ascii <= "MAC";
		else if (maccnt==C_CLENGTH)  state_ascii <= "DONE";
		else                         state_ascii <= "ERROR";
	end
	// synthesis translate_on
	
endmodule





