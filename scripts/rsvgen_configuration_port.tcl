set str "[rsv_print_license]
`timescale 1ns/1ps

import ovm_pkg::*;
import rsv_solyr_pkg::*;
import usr_solyr_pkg::*;

`include \"ovm_macros.svh\"
`include \"rsv_defines.svh\"

`define $cp_

module $cp_
#(parameter

`ifdef ICAP_VIRTEX4_WRAPPER
	ICAP_WIDTH = \"X8\"
`endif

`ifdef ICAP_VIRTEX5_WRAPPER
	ICAP_WIDTH = \"X8\"
`endif

`ifdef ICAP_VIRTEX6_WRAPPER
	ICAP_WIDTH = \"X8\"
`endif
	
`ifdef ICAPE2_WRAPPER
	DEVICE_ID  = 32'h03651093,
	ICAP_WIDTH = \"X8\",
	SIM_CFG_FILE_NAME = \"NONE\"
`endif

`ifdef ICAPE3_WRAPPER
	DEVICE_ID = 32'h03651093,
	ICAP_AUTO_SWITCH = \"DISABLE\",
	SIM_CFG_FILE_NAME = \"NONE\"
`endif

)
(

`ifdef ICAP_VIRTEX4_WRAPPER
	output     BUSY     ,
	output     \[31:0\] O ,
	input      CE       ,
	input      CLK      ,
	input      \[31:0\] I ,
	input      WRITE
`endif

`ifdef ICAP_VIRTEX5_WRAPPER
	output     BUSY     ,
	output     \[31:0\] O ,
	input      CE       ,
	input      CLK      ,
	input      \[31:0\] I ,
	input      WRITE
`endif

`ifdef ICAP_VIRTEX6_WRAPPER
	output     BUSY     ,
	output     \[31:0\] O ,
	input      CSB      ,
	input      CLK      ,
	input      \[31:0\] I ,
	input      RDWRB
`endif

`ifdef ICAPE2_WRAPPER
	output     \[31:0\] O ,
	input      CSIB     ,
	input      CLK      ,
	input      \[31:0\] I ,
	input      RDWRB
`endif

`ifdef ICAPE3_WRAPPER
	output     \[31:0\] O ,
	input      CSIB     ,
	input      CLK      ,
	input      \[31:0\] I ,
	input      RDWRB    ,
	output     AVAIL    ,
	output     PRDONE   ,
	output     PRERROR
`endif

);

	`define NUM_RR $l_ // Number of reconfigurable regions in the solyr

	// Instantiate the ICAP interface and assign the signals in the interface
	// with real values from the ICAP_VIRTEXx_WRAPPER

	icap_if iif();

	wire \[31:0\]       I_nbs;   // non-bitswapped version of incoming bitstream from I
	wire \[31:0\]       O_bs;    // bitswapped version of outgoing bitstream to O
	
	logic \[31:0\]      O_bs_d1;
	logic \[31:0\]      O_bs_d2;
	logic \[31:0\]      O_bs_d3;
	
`ifdef ICAP_VIRTEX4_WRAPPER
	assign iif.cclk        = CLK          ;
	assign iif.ccs_n       = CE           ;
	assign iif.cwe_n       = WRITE        ;
	assign BUSY            = iif.cbusy    ;
	assign iif.cdata       = I            ;
	assign O               = iif.cdata_rb ;
`endif

`ifdef ICAP_VIRTEX5_WRAPPER
	assign iif.cclk        = CLK          ;
	assign iif.ccs_n       = CE           ;
	assign iif.cwe_n       = WRITE        ;
	assign BUSY            = iif.cbusy    ;
	assign iif.cdata       = I_nbs        ;
	assign O               = O_bs ;
`endif

`ifdef ICAP_VIRTEX6_WRAPPER
	assign iif.cclk        = CLK          ;
	assign iif.ccs_n       = CSB          ;
	assign iif.cwe_n       = RDWRB        ;
	assign BUSY            = iif.cbusy    ;
	assign iif.cdata       = I_nbs        ;
	assign O               = O_bs         ;
`endif

`ifdef ICAPE2_WRAPPER
	assign iif.cclk        = CLK          ;
	assign iif.ccs_n       = CSIB         ;
	assign iif.cwe_n       = RDWRB        ;
	assign iif.cdata       = I_nbs        ;
	assign O               = O_bs_d2      ;
`endif

`ifdef ICAPE3_WRAPPER
	assign iif.cclk        = CLK          ;
	assign iif.ccs_n       = CSIB         ;
	assign iif.cwe_n       = RDWRB        ;
	assign iif.cdata       = I_nbs        ;
	assign O               = O_bs_d2      ;
	assign AVAIL           = iif.cavail   ;
	assign PRDONE          = iif.cprerror ;
	assign PRERROR         = iif.cprdone  ;
`endif

	// For Virtex5 and Virtex6, the bitstream need to be bitswapped before sending to 
	// the 32b ICAP interface. Here, the bitstream is swapped back to the original 
	// order before going into the class-bassed part of the simulation environment
	// 
	// For Virtex4, the bitstream is never swapped for 32b ICAP interface, so the 
	// following code is not used for Virtex4
	
	generate begin : gen_i_bitswap
		genvar j;
		for (j = 0; j <= 3; j = j + 1) begin : mirror_j
			genvar i;
			for (i = 0; i <= 7; i = i + 1) begin : mirror_i
				assign I_nbs\[j * 8 + i\] = I\[j * 8 + 7 - i\];
			end
		end
	end endgenerate

	generate begin : gen_o_bitswap
		genvar j;
		for (j = 0; j <= 3; j = j + 1) begin : mirror_j
			genvar i;
			for (i = 0; i <= 7; i = i + 1) begin : mirror_i
				assign O_bs\[j * 8 + i\] = iif.cdata_rb\[j * 8 + 7 - i\];
			end
		end
	end endgenerate
	
	// For 7SERIES and ULTRASCALE, the readback bitstream needs 2 additional cycles of delays.
	// (3 cycles in total). Note, iif.cdata_rb already has 1 cycle delay.
	
	always @(posedge CLK) begin
		O_bs_d1 <= O_bs;
		O_bs_d2 <= O_bs_d1;
		O_bs_d3 <= O_bs_d2;
	end
	
	initial begin

		// Configure the instance of ICAP port in the testbench:
		//
		// Pass the interface icap_if to the virtual interface in verification environment
		// Overides the default configuration port to the extended class
		//
		// Here, the settins are done by the configuration & factory mechanism of OVM
		// for details, see the OVM User Guide

		`set_config_interface(rsv_if_wrapper #(icap_if_type), \"*.ci\", \"iif_tag\", iif)
		
		rsv_configuration_port_base#(`NUM_RR)::type_id::set_type_override(rsv_configuration_port#(`NUM_RR)::get_type());
		rsv_configuration_interface_base::type_id::set_type_override(rsv_icap_virtex::get_type());
		rsv_configuration_parser_base#(`NUM_RR)::type_id::set_type_override(rsv_sbt_parser#(`NUM_RR)::get_type());

`ifdef ICAP_VIRTEX4_WRAPPER
		set_config_int(\"*.ci\", \"has_readback_delay\", 1);
`endif
`ifdef ICAP_VIRTEX5_WRAPPER
		set_config_int(\"*.ci\", \"has_readback_delay\", 1);
`endif
`ifdef ICAP_VIRTEX6_WRAPPER
		set_config_int(\"*.ci\", \"has_readback_delay\", 1);
`endif

	end

`ifdef MTI_QUESTA

	// Coverage Groups and Assertions
	
	property icap_if_cwe_n_stable;
		@(posedge iif.cclk) (iif.ccs_n == 1'b0) |=> (\$stable(iif.cwe_n) || (iif.ccs_n == 1'b1));
	endproperty
	assert_icap_if_cwe_n_stable : assert property (icap_if_cwe_n_stable);
	
	property icap_if_cdata_known;
		@(posedge iif.cclk) (iif.ccs_n == 1'b0) && (iif.cwe_n == 1'b0) |-> (!\$isunknown(iif.cdata));
	endproperty
	assert_icap_if_cdata_known : assert property (icap_if_cdata_known);
	
	property icap_if_cdata_rb_known;
		@(posedge iif.cclk) (iif.ccs_n == 1'b0) && (iif.cwe_n == 1'b1) |=> (!\$isunknown(iif.cdata_rb));
	endproperty
	assert_icap_if_cdata_rb_known : assert property (icap_if_cdata_rb_known);

`endif

endmodule

"
