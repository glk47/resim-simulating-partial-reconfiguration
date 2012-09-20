set str "[rsv_print_license]
`timescale 1ns/1ps

import ovm_pkg::*;
import rsv_solyr_pkg::*;
import usr_solyr_pkg::*;

`include \"ovm_macros.svh\"
`include \"rsv_defines.svh\"

// This is the dynamic part of the testbench, which is built on top of OVM
// using SystemVerilog. This module has no IO and can be instantiated inside a
// VHDL/Verilog/SystemVerilog testbench. You can also cut and paste the code
// into your top level testbench if it is written in SystemVerilog.

module $vf_
(

);

	`define NUM_RR $l_ // Number of reconfigurable regions in the solyr
	
	// Instantiate the simulation-only layer;
	// Create, parameterize, & run the solyr in the inital block

	rsv_solyr#(`NUM_RR) solyr;

	initial begin

		\$timeformat (-9, 3, \"ns\", 5);
		
		// Use factory override to replace the base classes with parameterized classes.
		// In particular, the following intial block parameterize the scoreboard artifact. 
		// See the OVM User Guide for factory overrides.
	
		rsv_scoreboard_base#(`NUM_RR)::type_id::set_type_override(${scb_}#(`NUM_RR)::get_type());
		
		// Create the simulation-only layer by calling the new constructor
		//
		// the 1st parameter is the name of the simulation-only layer,
		// the 2nd parameter is the parent of the simulation-only layer, which is null in this case
		//    (that means solyr is the top of class-based verification environment)

		solyr = new(\"solyr\", null);

		// After instantiation, call the run_test() method of solyr, which is
		// a built-in method provided by OVM. This methods calls all the phases of
		// ovm_component (new, build, connect, run, etc ...).
		//
		// The simulation-only layer will be configured with user-defined parameters and user-defined
		// derived classes. See OVM User Guide for details of configuration and factory mechanism. 
		
		solyr.run_test();
	end

endmodule


"
