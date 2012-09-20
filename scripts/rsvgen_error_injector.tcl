set str "[rsv_print_license]
`ifndef [string toupper ${ei_}]_SVH
`define [string toupper ${ei_}]_SVH

class ${ei_} extends rsv_error_injector#(virtual interface $ri_);

	// configuration table and parameters
	`ovm_component_utils_begin(${ei_})
	`ovm_component_utils_end

	// new - constructor
	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	// Define your own tasks to inject errors.
	// You should not change the name or the prototype of these tasks.
	// Possible injections include:
	//
	//     x, all-0, all-1, negate, random, no-change

	extern virtual protected task inject_to_static_module();
	extern virtual protected task inject_to_reconfigurable_module();
	extern virtual protected task inject_to_internal_signals();

endclass : ${ei_}

task ${ei_}::inject_to_static_module ();
	// TODO: Implement your own inject_to_static_module() task here
	// The following is an example of \"x\" injection to the static side

	rsv_ei_trans tr;
	realtime ei_time;

	// Enable the static error injection

	ei_vi.sei_en = 1'b1;
	
	// Use ei_vi.reconf_phase as a trigger to start error injection
	// ei_vi.reconf_phase is asserted during reconfiguration 
	
	@(posedge ei_vi.reconf_phase);
	
[rsv_print_x_injection $ri_ sei]

endtask : ${ei_}::inject_to_static_module

task ${ei_}::inject_to_reconfigurable_module ();
	// TODO: Implement your own inject_to_reconfigurable_module() task here
	// Typically, this task can manipulate signals (including the clock) to inject 
	// error to the current active reconfigurable module. The following is an  
	// example of \"x\" injection to the reconfigurable modules (dynamic side)

	// Enable the dynamic error injection

	ei_vi.dei_en = 1'b1;

	// Use ei_vi.reconf_phase as a trigger to start error injection
	// ei_vi.reconf_phase is asserted during reconfiguration 
	
	@(posedge ei_vi.reconf_phase);
	
[rsv_print_x_injection $ri_ dei]

endtask : ${ei_}::inject_to_reconfigurable_module

task ${ei_}::inject_to_internal_signals ();
	// TODO: Implement your own inject_to_internal_signals() task here. This 
	// task sets the type of internal error injection. When a module is swapped
	// out, the Simulator Kernel Thread (SKT) forces x, zero or random values
	// to all interal signals/memory cells of the ****DISABLED**** module. 
	//
	// Limited by the implementation of ReSim, IEI does not support VHDL signals
	// and Verilog nets. These signals are ignored. 

	ei_vi.iei_en = 1'b1;
	ei_vi.iei_sig_type = \"x\";    // \"none\", \"zero\" OR. \"x\"
	ei_vi.iei_mem_type = \"none\"; // \"none\", \"zero\" OR. \"rand\"
	
endtask : ${ei_}::inject_to_internal_signals

`endif // [string toupper ${ei_}]_SVH


"



