/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XDRS

 Create Date:    19/09/2010
 Design Name:    filter_sync

 *******************************************************************/

`timescale 1ns/1ns

module filter_sync
#(parameter
	INVALUE  = 32'h1,
	OUTVALUE = 32'h1
)
(
	input       clk       ,
	input       rstn      ,

	//-- to/from core----
	input       is_data_in,
	input       is_data_out,

	//-- to/from reconfiguration controller----
	input       rc_reqn,
	output reg  rc_ackn
);

//-------------------------------------------------------------------
// Signal Declaration
//-------------------------------------------------------------------

	/* reconfiguration fsm */
	reg [1:0] state_c, state_n;
	wire rc_is_idle;

	/* p_transaction_counter */
	wire [31:0] rc_tc;
	reg [31:0] rc_tc_0;
	wire [31:0] rc_tc_1;

//-------------------------------------------------------------------
// Transaction Counter
//-------------------------------------------------------------------

	/*
		note:
			when is_data_in == 1, fsm leave idle state immediately (combinational)
			when is_data_out == 1, fsm re-enter idle state at next cycle (sequentially)

		eg. assume the swapper get 2 data and send 2 data, the timing like this:
			is_data_in  _ _ _ - - _ _ _ _ _ _ _ _
			is_data_out _ _ _ _ _ _ _ _ - - _ _ _
			state       idle  in  proc  out idle
			rc_tc_0     0 0 0 0 1 2 2 2 2 1 0 0 0
			rc_tc_1     1 1 1 1 2 3 3 3 3 2 1 1 1
			tc          0 0 0 1 2 2 2 2 2 1 0 0 0
	*/
	/* p_transaction_counter: the add 1 value */
	assign rc_tc_1 = rc_tc_0 + INVALUE;
	/* p_transaction_counter: the current value */
	always @(posedge clk or negedge rstn) begin
		if (~rstn) begin
			rc_tc_0 <= 32'h0;
		end else begin
			if (is_data_in) rc_tc_0 <= rc_tc_0 + INVALUE;
			if (is_data_out) rc_tc_0 <= rc_tc_0 - OUTVALUE;
		end
	end
	/* p_transaction_counter: the true value */
	assign rc_tc = (is_data_in) ? rc_tc_1: rc_tc_0;
	assign rc_is_idle = (rc_tc == 32'h0);

//-------------------------------------------------------------------
// RC FSM - reconfiguration controller: decide a safe state
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


