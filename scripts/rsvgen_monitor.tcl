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

	// Define your own tasks to collect transactions
	// You should not change the name or the prototype of these tasks

	extern virtual protected task collect_unload_transaction();
	extern virtual protected task collect_activate_transaction();

endclass : ${mon_}

task ${mon_}::collect_unload_transaction();
	// TODO: Implement your own collect_unload_transaction() task here
	// The collect_unload_transaction() task typically inspects the signal
	// transitions on the virtual interface and generate the collected
	// \"unloading\" transactions towards the analysis port

	rsv_unload_trans tr;
	
	forever begin
		// TODO: waiting until a complete \"unloading\" operation is
		// observed on the virtual interface (e.g. the \"req, ack\" handshakes)

		// ... YOUR OWN CODE ...
		// e.g. @(posedge mon_vi.clk); ...
		break;

		// After an unloading operation is detected, create a new
		// transaction with the correct attribute(s) and write it to the
		// analysis port (ap)

		tr = new(\$realtime, \"Current module unloaded\", OVM_MEDIUM);
		
		`region_print_record_trans(get_parent(), tr);
		`region_analysis_port_trans(get_parent(), tr.clone());
		
	end

endtask : ${mon_}::collect_unload_transaction

task ${mon_}::collect_activate_transaction();
	// TODO: Implement your own collect_activate_transaction() task here
	// The collect_activate_transaction() task typically inspects the signal
	// transitions on the virtual interface and generate the collected
	// \"activation\" transactions towards the analysis port

	rsv_activate_trans tr;
	
	forever begin
		// TODO: waiting until a complete \"activation\" operation is
		// observed on the virtual interface (e.g. asserting the \"reset\" signal)

		// ... YOUR OWN CODE ...
		// e.g. @(posedge mon_vi.clk); ... 
		break;

		// After an activation operation is detected, create a new
		// transaction with the correct attribute(s) and write it to the
		// analysis port (ap)

		tr = new(\$realtime, \"New module activated\", OVM_MEDIUM);
		
		`region_print_record_trans(get_parent(), tr);
		`region_analysis_port_trans(get_parent(), tr.clone());
		
	end

endtask : ${mon_}::collect_activate_transaction

`endif // [string toupper ${mon_}]_SVH


"
