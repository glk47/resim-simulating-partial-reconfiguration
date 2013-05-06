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
	
	protected chandle interp;
	
	extern virtual task inject_errors(rsv_ei_trans tr);
	extern virtual protected task inject_to_static_module(rsv_ei_trans tr);
	extern virtual protected task inject_to_reconfigurable_module(rsv_ei_trans tr);
	extern virtual protected task inject_to_internal_signals(rsv_ei_trans tr);
	extern virtual protected task end_of_injecting_errors(rsv_ei_trans tr);
	
	virtual task run();
		interp = mti_Interp();
		
		ei_vi.sei_en <= 1'b0;
		ei_vi.dei_en <= 1'b0;
		
	endtask : run
	
endclass : rsv_error_injector

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

task rsv_error_injector::inject_errors(rsv_ei_trans tr);
	
	// At the beginning of error injection, this task calls the inject_to_static_module(), 
	// inject_to_reconfigurable_module() and inject_to_internal_signals() tasks to 
	// perform the error injection. At the end of error injection, this task calls 
	// the end_of_injecting_errors() task to clean up error injection. 
	// 
	// The error injector is typically re-defined by users. Users should override the 
	// three tasks for design-/test- specific error sources. The error sources can be 
	// undefined-x-values, stuck-to-0, stuck-to-1, random-signal-value, or some 
	// design-specific sequence of signal transition. 
	
	case (tr.op)
		WCFG: begin 
			if ((tr.rmid!=ei_vi.active_module_id)&&(tr.rmid!=8'hff)) begin
				fork
					inject_to_static_module(tr);
					inject_to_reconfigurable_module(tr);
					inject_to_internal_signals(tr);
				join_none
				tr.error_msg = "Starting Error Injection ...";
			end else begin
				tr.error_msg = "Error Injection not required ...";
			end
			
		end
		RCFG: begin tr.error_msg = "Error Injection not required ..."; end
		ENDCFG: begin 
			fork
				end_of_injecting_errors(tr); 
			join_none
			tr.error_msg = "End of Error Injection ..."; 
		end
		default: begin /* Ignore other operations */ end
	endcase
	
endtask : rsv_error_injector::inject_errors

task rsv_error_injector::inject_to_static_module(rsv_ei_trans tr);
	`ovm_warning("ReSim", "Using the default error injector")
endtask : rsv_error_injector::inject_to_static_module

task rsv_error_injector::inject_to_reconfigurable_module(rsv_ei_trans tr);
	`ovm_warning("ReSim", "Using the default error injector")
endtask : rsv_error_injector::inject_to_reconfigurable_module

task rsv_error_injector::inject_to_internal_signals(rsv_ei_trans tr);
	`ovm_warning("ReSim", "Using the default error injector")
endtask : rsv_error_injector::inject_to_internal_signals

task rsv_error_injector::end_of_injecting_errors(rsv_ei_trans tr);
	`ovm_warning("ReSim", "Using the default error injector")
endtask : rsv_error_injector::end_of_injecting_errors

`endif // RSV_ERROR_INJECTOR_SVH
