/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XDRS

 Create Date:    19/09/2010
 Design Name:    intern_sync

 *******************************************************************/

`timescale 1ns/1ns

module intern_sync
(
	input       clk       ,
	input       rstn      ,

	//-- to/from core----
	input       rc_is_idle,

	//-- to/from reconfiguration controller----
	input       rc_reqn,
	output reg  rc_ackn
);

//-------------------------------------------------------------------
// Signal Declaration
//-------------------------------------------------------------------

	/* reconfiguration fsm */
	reg [1:0] state_c, state_n;

//-------------------------------------------------------------------
// RC FSM - reconfiguration add-on: decide a safe state
//-------------------------------------------------------------------

	localparam [1:0]
		RC_Idle    = 4'd0,
		RC_ReqAck  = 4'd1;

	always @(posedge clk or negedge rstn) begin
		if (~rstn)
			state_c <= RC_Idle;
		else
			state_c <= state_n;
	end

	always @(*) begin
		{rc_ackn} = {1'b1};

		/*
			mealy fsm:

				the ack must rise at the same clock when is_idle comes in
				so that the static part can assert reset at the next cycle
				when the prm is (potentially) just about to leave the idle state

			timing diagram:

				reqn    => -1- _0_ _0_ _0_ -1- -1-
				is_idle <= -1- -1- -1- _0_ -1- -1-
				ackn    <= -1- -1- -1- _0_ -1- -1-
				restn   => -1- -1- -1- -1- _0_ _0_

				clk edge  |   |   |   |   |   |

		*/
		case (state_c)
			RC_Idle: begin state_n = (~rc_reqn)? RC_ReqAck:RC_Idle; end
			RC_ReqAck:begin
				if(rc_is_idle) begin
					state_n = RC_Idle;
					rc_ackn = 1'b0;
				end else begin
					state_n = RC_ReqAck;
				end
			end
			default: begin state_n = RC_Idle; end
		endcase
	end

endmodule


