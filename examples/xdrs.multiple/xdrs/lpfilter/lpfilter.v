//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: XDRS Demo
//
// Create Date:    17/07/2012
// Design Name:    lpfilter
//
//---------------------------------------------------------------------

`timescale 1ns/1ns

module lpfilter
#(parameter
	C_TYPE = 0
)
(
	input                 clk           ,
	input                 rstn          ,

	//-- to/from producer/consumer ----
	output                p_prdy        ,
	input                 p_crdy        , // TODO: NOT USED by the LowPass Filter
	input                 p_cerr        , // TODO: NOT USED by the LowPass Filter
	output     [31:0]     p_data        ,

	input                 c_prdy        ,
	output                c_crdy        ,
	output                c_cerr        ,
	input      [31:0]     c_data        ,
	
	//-- to/from reconfiguration controller----
	input                 rc_reqn       ,
	output                rc_ackn       

);
	
	wire        fir_nd;
	wire        fir_rfd;
	wire [15:0] fir_din;
	wire        start_sync;
	
	generate begin : gen_lpfir
		
		if (C_TYPE == 0) begin : gen_mac
			
			wire fir_rfd_from_core;
			gfirMAC #(
				.C_IWIDTH       (16),
				.C_OWIDTH       (32),
				.C_CWIDTH       (16),
				.C_CLENGTH      (21)
			) fir (
				.clk            ( clk        ),
				.sclr           ( ~rstn      ),
				.nd             ( fir_nd     ),
				.rfd            ( fir_rfd_from_core ),
				.rdy            ( p_prdy     ),
				.din            ( fir_din    ),
				.dout           ( p_data     )
			
			);
			assign fir_rfd = fir_rfd_from_core & rstn; // WAR. See demo2.bug.12
		
		end else if (C_TYPE == 1) begin : gen_tf
			
			gfirTF #(
				.C_IWIDTH       (16),
				.C_OWIDTH       (32),
				.C_CWIDTH       (16),
				.C_CLENGTH      (21)
			) fir (
				.clk            ( clk        ),
				.sclr           ( ~rstn      ),
				.en             ( fir_nd & rstn ), // WAR. See demo2.bug.12
				.din            ( fir_din    ),
				.dout           ( p_data     )
			);
			
			reg nd_1;
			always @(posedge clk) begin
				if (~rstn) begin
					nd_1 <= 1'b0;
				end else begin
					nd_1 <= fir_nd;
				end
			end
			assign p_prdy = nd_1;
			assign fir_rfd = 1'b1 & rstn; // WAR. See demo2.bug.12
			
		end
		
	end endgenerate
	
	assign fir_nd  = (start_sync)? 1'b1  : c_prdy;
	assign fir_din = (start_sync)? 16'h0 : c_data[15:0]; // TODO: Ignore MSB ????
	
	assign c_crdy  = (start_sync)? 1'b0 : fir_rfd;
	assign c_cerr  = (start_sync)? 1'b1 : 1'b0; // Cancel all requrests from consumer if (c_prdy)
	
	pipeline_sync #(
		.C_SYNCCNT      (32)
	) sync_0 (
		.clk            ( clk        ),
		.rstn           ( rstn       ),
		//-- to/from core----
		.rdy            ( p_prdy     ),
		.start_sync     ( start_sync ),
		//-- to/from reconfiguration controller----
		.rc_reqn        ( rc_reqn    ),
		.rc_ackn        ( rc_ackn    )
	);
	
endmodule



