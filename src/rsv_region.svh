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

`ifndef RSV_REGION_SVH
`define RSV_REGION_SVH

`include "rsv_portal_controller.svh"
`include "rsv_state_spy.svh"
`include "rsv_error_injector.svh"
`include "rsv_region_recorder.svh"

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_region extends rsv_region_base;

	//---------------------------------------------------------------------
	// port, channel & sub-components
	//---------------------------------------------------------------------
	
	rsv_portal_controller_base     pc;
	rsv_state_spy_base             ss;
	rsv_error_injector_base        ei;
	rsv_region_recorder_base       rec;

	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	`ovm_component_utils_begin(rsv_region)
	`ovm_component_utils_end

	//---------------------------------------------------------------------
	// constructor, build(), connect() & other ovm phase(s)
	//---------------------------------------------------------------------
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	virtual function void build();
		super.build();

		// Build the sub-components in the component heirachy. Here, all artifacts
		// are defined as handlers and the classes we instantiated are all base 
		// classes. Users can use factory overides to replace the base classes 
		// with user-defined derived classes as desired.
		// 
		// Typically, users should parameterize the derived classes with design-specific
		// information (e.g., RR boundary signals, RR size, etc...) and override the 
		// base classes with the derived classes

		pc  = rsv_portal_controller_base::type_id::create("pc", this);
		ss  = rsv_state_spy_base::type_id::create("ss", this);
		ei  = rsv_error_injector_base::type_id::create("ei", this);
		rec = rsv_region_recorder_base::type_id::create("rec", this);

	endfunction : build

	//---------------------------------------------------------------------
	// run()
	//---------------------------------------------------------------------
	
	// The run task read rsv_simop_trans from the port, and calls the member functions
	// of pc, ei, ss to process the transaction (e.g., module selection, error 
	// injection, state saving and restoration). It also calls the member function 
	// of the recoder for transaction visualization. 
	// 
	// Finially, it writes the processed transaction to the analysis port, through
	// which the scoreboard perfroms further analysis (e.g. coverage collection)
	
	virtual task run();
		rsv_simop_trans tr;
		
		rsv_cfg_trans  tr_0;
		rsv_ei_trans   tr_1;
		rsv_spy_trans  tr_2;
		
		forever begin
			get_p.get(tr);
	
			if ( $cast( tr_0, tr ) ) begin pc.select_module_phase(tr_0); end
			if ( $cast( tr_1, tr ) ) begin ei.inject_errors(tr_1); end
			if ( $cast( tr_2, tr ) ) begin ss.save_restore_state(tr_2); end
			
			rec.print_record_trans(tr);

			-> tr.done;
			ap.write(tr.clone());

		end
		
	endtask : run

endclass : rsv_region

`endif // RSV_REGION_SVH
