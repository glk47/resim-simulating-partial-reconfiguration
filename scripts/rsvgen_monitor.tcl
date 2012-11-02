set str "[rsv_print_license]
`ifndef [string toupper ${mon_}]_SVH
`define [string toupper ${mon_}]_SVH

class ${mon_} extends rsv_monitor#(virtual interface $ri_);

	// configuration table and parameters
	`ovm_component_utils_begin(${mon_})
	`ovm_component_utils_end

	// new - constructor
	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	// Define your own tasks to visualize the SBT transactions
	// You should not change the name or the prototype of these tasks

	extern virtual task print_record_trans(rsv_sbt_trans tr);

endclass : ${mon_}

task ${mon_}::print_record_trans(rsv_sbt_trans tr);
	// TODO: Implement your own print_record_trans() task here
	// The print_record_trans() task typically interprets and prints
	// the SBT transaction. 

endtask : ${mon_}::print_record_trans

`endif // [string toupper ${mon_}]_SVH


"
