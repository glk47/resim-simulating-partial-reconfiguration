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

`ifndef RSV_PORTAL_CONTROLLER_SVH
`define RSV_PORTAL_CONTROLLER_SVH

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_portal_controller#(type IF=virtual interface null_if) extends rsv_portal_controller_base;

	//---------------------------------------------------------------------
	// virtual interface(s)
	//---------------------------------------------------------------------
	
	IF pc_vi;
	virtual function void register_if(IF pc_);
		pc_vi = pc_;
	endfunction : register_if

	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	protected int num_rm = 1;
	protected string rr_inst = "";
	`ovm_component_param_utils_begin(rsv_portal_controller#(IF))
		`ovm_field_int(num_rm, OVM_ALL_ON)
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
		`get_config_interface(rsv_if_wrapper#(IF),"pif_tag",pc_vi)
	endfunction : build
	
	//---------------------------------------------------------------------
	// run(), member tasks & member variables
	//---------------------------------------------------------------------
	
	`define PORTAL_CONNECT_TO_ERROR_INJECTOR 1'h1
	`define PORTAL_RESUME_NORMAL_CONNECTION 1'h0
	
	extern virtual task select_module_phase(rsv_cfg_trans tr); 
	extern virtual protected task portal_do_wcfg(rsv_cfg_trans tr); 
	extern virtual protected task portal_do_rcfg(rsv_cfg_trans tr); 
	extern virtual protected task portal_do_endcfg(rsv_cfg_trans tr); 

	virtual task run();
		
		pc_vi.active_module_id <= 8'h0;
		pc_vi.reconf_phase <= `PORTAL_RESUME_NORMAL_CONNECTION;

	endtask : run
		
endclass : rsv_portal_controller

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

task rsv_portal_controller::select_module_phase(rsv_cfg_trans tr);

	// The select_module_phase task performs configuration operations according to
	// the incomming transaction. It (1) drives the configuration phase and (2),
	// selects the current active module
	
	case (tr.op)
		WCFG: begin portal_do_wcfg(tr); end
		RCFG: begin portal_do_rcfg(tr); end
		ENDCFG: begin portal_do_endcfg(tr); end
		default: begin /* Ignore other operations */ end
	endcase

endtask : rsv_portal_controller::select_module_phase

task rsv_portal_controller::portal_do_wcfg(rsv_cfg_trans tr);

	if (tr.rmid == 8'hff) begin
		
		// Writing a mask SBT: do nothing significant here
		
		tr.name = $psprintf("RR%0d.mask",tr.rrid);
		
	end else begin
		`check_error(tr.rmid<=num_rm, $psprintf("RMid(0x%0h) <= 0x%0h",tr.rmid,num_rm))
		
		// Upon receiving a "wcfg" transaction, the portal controller 
		// selects the new module as the current active reconfigurable module
		
		// Meanwile, the portal controller also drives the portal into DURING phase, 
		// during which the static part and the reconfigurable modules are connected to
		// the error injector. 
		
		if (pc_vi.active_module_id != tr.rmid) begin
			pc_vi.active_module_id <= tr.rmid;
			pc_vi.reconf_phase <= `PORTAL_CONNECT_TO_ERROR_INJECTOR;
			
		end
		tr.name = $psprintf("%s.rm%0d(%s)",rr_inst,tr.rmid,pc_vi.module_names[tr.rmid]);
	end
	
endtask : rsv_portal_controller::portal_do_wcfg

task rsv_portal_controller::portal_do_rcfg(rsv_cfg_trans tr);

	if (tr.rmid == 8'hff) begin
		
		// Reading a mask SBT: do nothing significant here
		
		tr.name = $psprintf("RR%0d.mask",tr.rrid);
		
	end else begin
		`check_error(tr.rmid==pc_vi.active_module_id, $psprintf("RMid(0x%0h) == 0x%0h",tr.rmid,pc_vi.active_module_id))
		
		// Upon receiving a "rcfg" transaction, the portal does nothing but
		// switch back to the normal connection. No errors are injected when rcfg
		
		pc_vi.reconf_phase <= `PORTAL_RESUME_NORMAL_CONNECTION;
		tr.name = $psprintf("%s.rm%0d(%s)",rr_inst,tr.rmid,pc_vi.module_names[tr.rmid]);
		
	end
endtask : rsv_portal_controller::portal_do_rcfg

task rsv_portal_controller::portal_do_endcfg(rsv_cfg_trans tr);
	
	// Upon receiving a "endcfg" transaction, the portal is switched back 
	// to NORMAL phase in which the static part is connected to the current active
	// reconfigurable module. 
	
	pc_vi.reconf_phase <= `PORTAL_RESUME_NORMAL_CONNECTION;
	tr.name = $psprintf("%s.rm%0d(%s)",rr_inst,pc_vi.active_module_id,pc_vi.module_names[pc_vi.active_module_id]);
	
	
endtask : rsv_portal_controller::portal_do_endcfg
	
`endif // RSV_PORTAL_CONTROLLER_SVH
