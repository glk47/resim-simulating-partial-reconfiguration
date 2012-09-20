//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: XDRS Demo
//
// Create Date:    17/07/2012
// Design Name:    region_wrapper
//
//---------------------------------------------------------------------

`timescale 1ns/1ns

module region_wrapper
#(parameter
	RRID = 0
)
(
	input                 clk           ,
	input                 rstn          ,

	//-- to/from producer/consumer ----
	output                p_prdy        ,
	input                 p_crdy        ,
	input                 p_cerr        ,
	output     [31:0]     p_data        ,

	input                 c_prdy        ,
	output                c_crdy        ,
	output                c_cerr        ,
	input      [31:0]     c_data        ,
	
	//-- to/from reconfiguration controller----
	input                 rc_reqn       ,
	output                rc_ackn       ,
	
	input                 is_reconfn    

);

	wire                  rc_ackn_rr ;
	wire                  p_prdy_rr  ;
	wire       [31:0]     p_data_rr  ;
	wire                  c_crdy_rr  ;
	wire                  c_cerr_rr  ;
	
	generate begin : gen_rr
		
		if (RRID == 0) begin : gen_0
			
			math_0_rr math_0 (
				.clk              (clk                ),
				.rstn             (rstn               ),
				
				.p_prdy           (p_prdy_rr          ),
				.p_crdy           (p_crdy             ),
				.p_cerr           (p_cerr             ),
				.p_data           (p_data_rr          ),
				
				.c_prdy           (c_prdy             ),
				.c_crdy           (c_crdy_rr          ),
				.c_cerr           (c_cerr_rr          ),
				.c_data           (c_data             ),
				
				.rc_reqn          (rc_reqn            ),
				.rc_ackn          (rc_ackn_rr         )
			);
			
		end else if (RRID == 1) begin : gen_1
			
			math_1_rr math_1 (
				.clk              (clk                ),
				.rstn             (rstn               ),
				
				.p_prdy           (p_prdy_rr          ),
				.p_crdy           (p_crdy             ),
				.p_cerr           (p_cerr             ),
				.p_data           (p_data_rr          ),
				
				.c_prdy           (c_prdy             ),
				.c_crdy           (c_crdy_rr          ),
				.c_cerr           (c_cerr_rr          ),
				.c_data           (c_data             ),
				
				.rc_reqn          (rc_reqn            ),
				.rc_ackn          (rc_ackn_rr         )
			);
			
		end else if (RRID == 2) begin : gen_2
			
			lpfilter_2_rr lpfilter_2 (
				.clk              (clk                ),
				.rstn             (rstn               ),
				
				.p_prdy           (p_prdy_rr          ),
				.p_crdy           (p_crdy             ),
				.p_cerr           (p_cerr             ),
				.p_data           (p_data_rr          ),
				
				.c_prdy           (c_prdy             ),
				.c_crdy           (c_crdy_rr          ),
				.c_cerr           (c_cerr_rr          ),
				.c_data           (c_data             ),
				
				.rc_reqn          (rc_reqn            ),
				.rc_ackn          (rc_ackn_rr         )
			);
			
		end
		
	end endgenerate
			
	isolator isol_0 (
		//-- to/from reconfiguration-add-ons----
		.rc_ackn_rr       (rc_ackn_rr         ),
		.rc_ackn          (rc_ackn            ),
		//-- to/from producer/consumer ----
		.p_prdy           (p_prdy             ),
		.p_prdy_rr        (p_prdy_rr          ),
		.p_data           (p_data             ),
		.p_data_rr        (p_data_rr          ),
		
		.c_crdy           (c_crdy             ),
		.c_crdy_rr        (c_crdy_rr          ),
		.c_cerr           (c_cerr             ),
		.c_cerr_rr        (c_cerr_rr          ),
		//-- to/from reconfiguration manager----
		.is_reconfn       (is_reconfn         )
	);
	
endmodule



