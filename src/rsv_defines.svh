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

`ifndef RSV_DEFINES_SVH
`define RSV_DEFINES_SVH

`define print_info(tag, msg, ver) begin         \
	if (ovm_report_enabled(ver, OVM_INFO, tag)) \
		ovm_report_info (tag, msg, ver);        \
end

`define check_warning(cond, msg) if(!(cond)) begin `ovm_warning("ReSim", msg) end
`define check_error(cond, msg) if(!(cond)) begin `ovm_error("ReSim", msg) end
`define check_fatal(cond, msg) if(!(cond)) begin `ovm_fatal("ReSim", msg) end

`define region_print_record_trans(rr_, tr_) begin \
	rsv_region rr;                              \
	`check_error($cast(rr, rr_), $psprintf("Fail to cast to a Reconfigurable Region")) \
	rr.rec.print_record_trans(tr_);             \
end

`define region_analysis_port_trans(rr_, tr_) begin \
	rsv_region rr;                              \
	`check_error($cast(rr, rr_), $psprintf("Fail to cast to a Reconfigurable Region")) \
	rr.ap.write(tr_);                           \
end

`define get_config_interface(wrapper_,tag_,vi_) begin \
	automatic ovm_object obj;                   \
	automatic wrapper_ wrp;                     \
	`check_error(get_config_object(tag_, obj, 0), $psprintf("Interface wrapper (%s) not found",tag_)) \
	`check_error($cast(wrp, obj), $psprintf("Interface wrapper (%s) cast failed",tag_)) \
	vi_ = wrp.vi;                               \
end

`define set_config_interface(wrapper_, path_, tag_, vi_) begin   \
	automatic wrapper_ wrp = new (tag_, vi_);   \
	set_config_object(path_, tag_, wrp, 0);     \
end

`define rsv_module_inst(rr_, id_) $psprintf("%s.rm%d",rr_,id_)
`define rsv_module_inst_type(rr_, id_, nm_) $psprintf("%s.rm%d(%s)",rr_,id_,nm_)

`define rsv_execute_tcl(interp, cmd_) begin     \
	`check_error(mti_Cmd(cmd_)==0, Tcl_GetStringResult(interp)) \
	Tcl_ResetResult(interp);                    \
end
	
typedef virtual interface null_if null_if_type;
typedef virtual interface icap_if icap_if_type;
typedef virtual interface error_if error_if_type;

/*
	`define rsv_state_spy_decl_vhdl(if_, far_, tmp_, tmp_rb_, nm_, w_) \
		wire   [w_-1:0] tmp_;                                          \
		wire   [w_-1:0] tmp_rb_;                                       \
		assign tmp_ = if_.far[far_][w_-1:0];                           \
		assign if_.far_rb[far_][w_-1:0] = tmp_rb_;                     \
		assign if_.far_nm[far_] = nm_;
	
	`define rsv_state_spy_init_vhdl(tmp_, tmp_rb_, hdl_) begin         \
		$init_signal_driver(hdl_,tmp_rb_, , ,1);                       \
		$init_signal_driver(tmp_,hdl_   , , ,1);                       \
	end
	
	`define rsv_state_spy_decl_verilog(if_, far_, hdl_, nm_, w_)       \
		assign hdl_ = if_.far[far_][w_-1:0];                           \
		assign if_.far_rb[far_][w_-1:0] = hdl_;                        \
		assign if_.far_nm[far_] = nm_;
		
	`define rsv_cmem_init_vhdl_verilog(if_, sg_, nm_)                  \
		if_.signature  = sg_;                                          \
		if_.name       = nm_;
*/

`endif
