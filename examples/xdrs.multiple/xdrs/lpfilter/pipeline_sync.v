/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XDRS

 Create Date:    19/09/2010
 Design Name:    pipeline_sync

 *******************************************************************/

`timescale 1ns/1ns

module pipeline_sync
#(parameter
	C_SYNCCNT = 32
)
(
	input       clk       ,
	input       rstn      ,

	//-- to/from core----
	input                         rdy           ,
	output                        start_sync    ,

	//-- to/from reconfiguration controller----
	input       rc_reqn,
	output      rc_ackn
);

	localparam [1:0]
		IDLE = 4'd0,
		SYNC = 4'd1;
		
	reg [7:0] state_c, state_n;
	reg [31:0] synccnt; 
	wire is_end_sync;
	
//-------------------------------------------------------------------
// Main FSM
//-------------------------------------------------------------------
	
	always @(posedge clk or negedge rstn) begin
		if (~rstn)
			state_c <= IDLE;
		else
			state_c <= state_n;
	end
	
	always @(*) begin
		case (state_c)
			IDLE: begin state_n = (~rc_reqn)? SYNC: IDLE; end
			SYNC: begin state_n = (is_end_sync)? IDLE: SYNC; end
			default: begin state_n = IDLE; end
		endcase
	end
	
	assign start_sync = (state_c==SYNC);
	
//-------------------------------------------------------------------
// Pipeline_Sync Counter
//-------------------------------------------------------------------
	
	always @(posedge clk or negedge rstn) begin
		if (~rstn) begin
			synccnt <= 32'h0;
		end else begin
			if (is_end_sync) begin
				synccnt <= 32'h0;
			end else if (state_c==SYNC) begin
				if (rdy)
					synccnt <= synccnt+1'b1;
			end
		end
	end
	assign is_end_sync = ((synccnt+1'b1 == C_SYNCCNT) & rdy);
	assign rc_ackn = ~((synccnt+1'b1 == C_SYNCCNT) & rdy); // ~is_end_sync
	
endmodule


