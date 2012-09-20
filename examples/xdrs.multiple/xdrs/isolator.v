/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XDRS

 Create Date:    5/11/2010
 Design Name:    isolator

 *******************************************************************/

`timescale 1ns/1ns
	
module isolator
(
	//-- to/from reconfiguration-add-ons----
	input                 rc_ackn_rr    ,
	output                rc_ackn       ,

	//-- to/from producer/consumer ----
	output                p_prdy        ,
	output     [31:0]     p_data        ,
	output                c_crdy        ,
	output                c_cerr        ,
	
	input                 p_prdy_rr     ,
	input      [31:0]     p_data_rr     ,
	input                 c_crdy_rr     ,
	input                 c_cerr_rr     ,
	
	//-- to/from reconfiguration controller----
	input                 is_reconfn
);

//-------------------------------------------------------------------
// Signal Declaration
//-------------------------------------------------------------------
	
	assign rc_ackn    = (~is_reconfn)? 1'b1: rc_ackn_rr;
	assign p_prdy     = (~is_reconfn)? 1'b0: p_prdy_rr;
	assign p_data     = (~is_reconfn)? 32'h0: p_data_rr;
	assign c_crdy     = (~is_reconfn)? 1'b0: c_crdy_rr;
	
	// set error signal to default 1'b1 to indicate that the region 
	// is undergoing partial reconfiguration. 
	
	assign c_cerr     = (~is_reconfn)? 1'b1: c_cerr_rr;
	
endmodule



