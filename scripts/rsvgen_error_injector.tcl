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

	extern virtual protected task inject_to_static_module(rsv_ei_trans tr);
	extern virtual protected task inject_to_reconfigurable_module(rsv_ei_trans tr);
	extern virtual protected task inject_to_internal_signals(rsv_ei_trans tr);
	extern virtual protected task end_of_injecting_errors(rsv_ei_trans tr);

endclass : ${ei_}

task ${ei_}::inject_to_static_module (rsv_ei_trans tr);
	// TODO: Implement your own inject_to_static_module() task here
	// The following is an example of \"x\" injection to the static module

	// Enable the static error injection. By default, SEI is disabled. 

	ei_vi.sei_en <= 1'b1;
	
	// Use ei_vi.reconf_phase as a trigger to start error injection
	// ei_vi.reconf_phase is asserted during reconfiguration 
	
	@(posedge ei_vi.reconf_phase);
	
[rsv_print_x_injection $ri_ sei]

endtask : ${ei_}::inject_to_static_module

task ${ei_}::inject_to_reconfigurable_module (rsv_ei_trans tr);
	// TODO: Implement your own inject_to_reconfigurable_module() task here
	// Typically, this task can manipulate signals (including the clock) to inject 
	// error to the ****NEWLY-CONFIGURED**** reconfigurable module. The following is an  
	// example of \"x\" injection to the reconfigurable modules

	// Enable the dynamic error injection. By default, DEI is disabled. 

	ei_vi.dei_en <= 1'b1;

	// Use ei_vi.reconf_phase as a trigger to start error injection
	// ei_vi.reconf_phase is asserted during reconfiguration 
	
	@(posedge ei_vi.reconf_phase);
	
[rsv_print_x_injection $ri_ dei]

endtask : ${ei_}::inject_to_reconfigurable_module

task ${ei_}::inject_to_internal_signals (rsv_ei_trans tr);
	// TODO: Implement your own inject_to_internal_signals() task here. 
	// Typically, the tasks inject errors to the internal signals of 
	// the reconfigurable module. 
	// 
	// By evaluating the \"rsv_iei_hdl_state\" API in the Simulator Kernel 
	// Thread (SKT), the following example injects \"x\" to the ****OLD**** 
	// reconfigurable module. Limited by the implementation of ReSim, 
	// \"rsv_iei_hdl_state\" does not support VHDL signals and Verilog
	// nets and these signals are ignored. 
	
	logic \[7:0\] old_rmid = ei_vi.active_module_id;
	logic \[7:0\] new_rmid = tr.rmid;
	
	`rsv_execute_tcl(interp, \$psprintf(\"ReSim::rsv_iei_hdl_state %s rm%0d x none\",rr_inst,old_rmid))
	
	// Users can add other code here to perform design-specific error injection
	// operations. For example, users can \"force\" a particular signal instead 
	// of injecting error to all signals, or to use the \"mem load\" command to 
	// change the content of memory elements of the reconfigurable module. 
	
endtask : ${ei_}::inject_to_internal_signals

task ${ei_}::end_of_injecting_errors (rsv_ei_trans tr);
	// TODO: Implement your own end_of_injecting_errors() task here. 
	// Typically, this task cleans up and pending operations and ends the 
	// error injection operation
	
endtask : ${ei_}::end_of_injecting_errors

`endif // [string toupper ${ei_}]_SVH


"



