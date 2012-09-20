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
 *    contributors may be used to endorse or promote products derived from this 
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

`ifndef RSV_ERROR_INJECTOR_SVH
`define RSV_ERROR_INJECTOR_SVH

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_error_injector#(type IF=virtual interface null_if) extends rsv_error_injector_base;

	//---------------------------------------------------------------------
	// virtual interface(s)
	//---------------------------------------------------------------------
	IF sei_vi; // Error injection to the static side
	IF dei_vi; // Error injection to the dynamic side
	error_if_type ei_vi; // Error injection control signals

	virtual function void register_if(IF sei_, dei_, error_if_type ei_);
		sei_vi = sei_;
		dei_vi = dei_;
		ei_vi = ei_;
	endfunction : register_if

	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	protected string rr_inst = "";
	`ovm_component_param_utils_begin(rsv_error_injector#(IF))
		`ovm_field_string(rr_inst, OVM_ALL_ON)
	`ovm_component_utils_end

	//---------------------------------------------------------------------
	// constructor, build(), connect() & other ovm phase(s)
	//---------------------------------------------------------------------
	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	virtual function void build();
		super.build();
		`get_config_interface(rsv_if_wrapper #(IF),"sei_tag",sei_vi)
		`get_config_interface(rsv_if_wrapper #(IF),"dei_tag",dei_vi)
		`get_config_interface(rsv_if_wrapper #(error_if_type),"ei_tag",ei_vi)
	endfunction : build

	//---------------------------------------------------------------------
	// run(), member tasks & member variables
	//---------------------------------------------------------------------
	
	// The error injector is typically re-defined by users. Users should 
	// initialize the error sources in the run task, and define error injection
	// tasks tailer to design-/test- specific needs. 
	//
	// For example, the error sources can be undefined-x-values, stuck-to-0,
	// stuck-to-1, random-signal-value, or some design-specific sequence of 
	// signal transition. 
	
	virtual task run();
		fork
			inject_to_static_module();
			inject_to_reconfigurable_module();
			inject_to_internal_signals();
		join_none
	endtask : run

	virtual protected task inject_to_static_module();
		`ovm_warning("ReSim", "Using the default error injector")
	endtask : inject_to_static_module

	virtual protected task inject_to_reconfigurable_module();
		`ovm_warning("ReSim", "Using the default error injector")
	endtask : inject_to_reconfigurable_module
	
	virtual protected task inject_to_internal_signals();
		`ovm_warning("ReSim", "Using the default error injector")
	
		ei_vi.iei_en = 1'b0;
		ei_vi.iei_sig_type = "none"; // none, zero OR. x
		ei_vi.iei_mem_type = "none"; // none, zero OR. rand
		
	endtask : inject_to_internal_signals
	
endclass : rsv_error_injector

`endif // RSV_ERROR_INJECTOR_SVH
