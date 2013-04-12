set str "[rsv_print_license]
`ifndef [string toupper ${rec_}]_SVH
`define [string toupper ${rec_}]_SVH

class ${rec_} extends rsv_region_recorder#(virtual interface $ri_);

	// configuration table and parameters
	`ovm_component_utils_begin(${rec_})
	`ovm_component_utils_end

	// new - constructor
	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	// Define your own tasks to visualize the simop transactions
	// You should not change the name or the prototype of these tasks

	extern virtual task print_record_trans(rsv_simop_trans tr);

endclass : ${rec_}

task ${rec_}::print_record_trans(rsv_simop_trans tr);
	// TODO: Implement your own print_record_trans() task here
	// The print_record_trans() task typically interprets and prints
	// the simop transaction. 

endtask : ${rec_}::print_record_trans

`endif // [string toupper ${rec_}]_SVH


"
