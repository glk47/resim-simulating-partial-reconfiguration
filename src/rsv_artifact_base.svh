/*******************************************************************************
 * Copyright (c) 2012, Lingkan Gong
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *  * Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 *  * Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 *  * Neither the name of the copyright holder(s) nor the names of its
 *    contributor(s) may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
*******************************************************************************/

`ifndef RSV_REGION_COMPONENT_BASE_SVH
`define RSV_REGION_COMPONENT_BASE_SVH

// The base classes define the TLM communication channel (port/expor/imp)
// of simulation-only artifacts. By connecting instances of the base classes, 
// the simulation-only thereby defines the flow of transactions/operations.
//
// The detailed implementation of individual artifacts are defined in
// the derived classes, and can either be parameterized or overwritten by users.
// In particular, users must parameterize the virtual interfaces with real
// interfaces so as to establish the connection between the module-based user 
// design and the class-based verification environment

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_region_base extends ovm_component;

	// Port: get_p -- get port
	//       ap -- analysis port
	//
	// Through the get_p port, the derived class (i.e. rsv_region) typically
	// get a transation, and performs the required operation in the transaction. 
	// 
	// After processing the transaction, the derived class typically writes the
	// finalized transactions to the analysis port, through which further analysis
	// (e.g. coerage) is performed

	ovm_blocking_get_port #(rsv_simop_trans) get_p;
	ovm_analysis_port #(rsv_simop_trans) ap;

	`ovm_component_utils_begin(rsv_region_base)
	`ovm_component_utils_end

	// Function: new
	//
	// The new constructor creates the super class and instantiates the
	// TLM ports/exports (get_p, ap).

	function new (string name, ovm_component parent);
		super.new(name, parent);
		get_p = new ("get_p", this);
		ap = new("ap", this);
	endfunction : new

	// Task: run
	//
	// The run task will be called automatically by the OVM library. The base
	// class provides a default implementation which simply re-direct all incomming
	// transactions to the analysis port

	virtual task run();
		rsv_simop_trans tr;

		forever begin
			get_p.get(tr);
			
			`ovm_warning("ReSim", "Using the abstract class")

			ap.write(tr.clone());
		end
	endtask : run

endclass : rsv_region_base

class rsv_portal_controller_base extends ovm_component;

	`ovm_component_utils_begin(rsv_portal_controller_base)
	`ovm_component_utils_end

	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	virtual task select_module_phase(rsv_cfg_trans tr);
		`ovm_warning("ReSim", "Using the abstract class")
	endtask : select_module_phase

endclass : rsv_portal_controller_base

class rsv_state_spy_base extends ovm_component;

	`ovm_component_utils_begin(rsv_state_spy_base)
	`ovm_component_utils_end

	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	virtual task save_restore_state(rsv_spy_trans tr);
		`ovm_warning("ReSim", "Using the abstract class")
	endtask : save_restore_state

endclass : rsv_state_spy_base

class rsv_error_injector_base extends ovm_component;

	`ovm_component_utils_begin(rsv_error_injector_base)
	`ovm_component_utils_end

	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new
	
	virtual task inject_errors(rsv_ei_trans tr);
		`ovm_warning("ReSim", "Using the abstract class")
	endtask : inject_errors
	
endclass : rsv_error_injector_base

class rsv_region_recorder_base extends ovm_component;

	`ovm_component_utils_begin(rsv_region_recorder_base)
	`ovm_component_utils_end

	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	virtual task print_record_trans(rsv_simop_trans tr);
		`ovm_warning("ReSim", "Using the abstract class")
	endtask : print_record_trans
	
endclass : rsv_region_recorder_base

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_scoreboard_base#(int NUM_RR = 1) extends ovm_component;

	// Port: get_p -- get port
	//
	// Through the get_p port, the derived class (i.e. rsv_scoreboard)
	// typically get a transation, and performs coverag analysis

	ovm_blocking_get_port #(rsv_simop_trans) get_p;

	`ovm_component_param_utils_begin(rsv_scoreboard_base#(NUM_RR))
	`ovm_component_utils_end

	// Function: new
	//
	// The new constructor creates the super class and instantiates the
	// TLM ports/exports (get_p).

	function new (string name, ovm_component parent);
		super.new(name, parent);
		get_p = new("get_p", this);
	endfunction : new

	// Task: run
	//
	// The run task will be called automatically by the OVM library. The base
	// class provides a default implementation which simply print an warning 
	// message without processing any transactions

	virtual task run();
		`ovm_warning("ReSim", "Using the abstract class")
	endtask : run

endclass : rsv_scoreboard_base

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_configuration_port_base#(int NUM_RR = 1) extends ovm_component;

	// Port: put_p -- put port
	//
	// Through the put port, the derived class (e.g. rsv_configuration_port) typically
	// send the converted simop transations, which are typically passed to the  
	// reconfigurable regions, and initiates simulation-only tasks such as 
	// selecting the current active module and the reconfiguration phase.
	
	ovm_blocking_put_port #(rsv_simop_trans) put_p[NUM_RR];

	`ovm_component_param_utils_begin(rsv_configuration_port_base#(NUM_RR))
	`ovm_component_utils_end
	
	// Function: new
	//
	// The new constructor creates the super class and instantiates the
	// TLM ports/exports (put_p[]). 
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
		for (int i = 0; i<NUM_RR; i++) begin
			put_p[i] = new($psprintf("put_p[%0d]", i), this);
		end
	endfunction : new
		
	// Task: run
	//
	// The run task will be called automatically by the OVM library. The base  
	// class provides a default implementation which simply print an warning 
	// message without generating any transactions
	
	virtual task run();
		`ovm_warning("ReSim", "Using the abstract class")
	endtask : run

endclass : rsv_configuration_port_base

class rsv_configuration_interface_base extends ovm_component;

	// Port: put_p -- put port
	//
	// Through the put port, the derived class (e.g. rsv_icap_virtex) typically
	// send raw configuration data transations, which will be parsed and converted
	// to the simop transactions.
	
	ovm_blocking_put_port #(rsv_cdata_trans) put_p;

	`ovm_component_utils_begin(rsv_configuration_interface_base)
	`ovm_component_utils_end
	
	// Function: new
	//
	// The new constructor creates the super class and instantiates the
	// TLM ports/exports (put_p).
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
		put_p = new("put_p", this);
	endfunction : new
		
	// Task: run
	//
	// The run task will be called automatically by the OVM library. The base  
	// class provides a default implementation which simply print an warning 
	// message without generating any transactions
	
	virtual task run();
		`ovm_warning("ReSim", "Using the abstract class")
	endtask : run

endclass : rsv_configuration_interface_base

class rsv_configuration_parser_base#(int NUM_RR = 1) extends ovm_component;

	// Port: get_p   -- get port
	// Port: put_p[] -- put port
	//
	// Through the get port, the derived class (i.e. rsv_sbt_parser) typically
	// gets raw configuration data (configuration or readback), and converts 
	// raw transaction into simop transactions. 
	//
	// Through the put port, the derived class (i.e. rsv_sbt_parser) typically
	// send the converted simop transations, which are typically passed to the  
	// reconfigurable regions, and initiates simulation-only tasks such as 
	// selecting the current active module and the reconfiguration phase.
	
	ovm_blocking_get_port #(rsv_cdata_trans) get_p;
	ovm_blocking_put_port #(rsv_simop_trans) put_p[NUM_RR];

	`ovm_component_param_utils_begin(rsv_configuration_parser_base#(NUM_RR))
	`ovm_component_utils_end
	
	// Function: new
	//
	// The new constructor creates the super class and instantiates the
	// TLM ports/exports (get_p, put_p[]). 
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
		get_p = new("get_p", this);
		for (int i = 0; i<NUM_RR; i++) begin
			put_p[i] = new($psprintf("put_p[%0d]", i), this);
		end
	endfunction : new
		
	// Task: run
	//
	// The run task will be called automatically by the OVM library. The base  
	// class provides a default implementation which simply print an warning 
	// message without processing any transactions
	
	virtual task run();
		`ovm_warning("ReSim", "Using the abstract class")
	endtask : run

endclass : rsv_configuration_parser_base

`endif // RSV_REGION_COMPONENT_BASE_SVH
