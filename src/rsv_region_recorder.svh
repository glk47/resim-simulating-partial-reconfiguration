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

`ifndef RSV_REGION_RECORDER_SVH
`define RSV_REGION_RECORDER_SVH

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_region_recorder#(type IF=virtual interface null_if) extends rsv_region_recorder_base;

	//---------------------------------------------------------------------
	// virtual interface(s)
	//---------------------------------------------------------------------
	
	IF rec_vi;
	virtual function void register_if(IF rec_);
		rec_vi = rec_;
	endfunction : register_if

	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	protected int is_record_trans = 0;
	protected string rr_inst = "";
	`ovm_component_param_utils_begin(rsv_region_recorder#(IF))
		`ovm_field_int(is_record_trans, OVM_ALL_ON)
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
		`get_config_interface(rsv_if_wrapper#(IF),"rec_tag",rec_vi)
	endfunction : build

	//---------------------------------------------------------------------
	// run(), member tasks & member variables
	//---------------------------------------------------------------------
	
	integer sbt_stream_h=0;
	integer sbt_trans_h=0;
	extern virtual task print_record_trans(rsv_simop_trans tr);
	
	// The run task initialize the transaction stream to be visualized

	virtual task run();
		if (is_record_trans) begin
			sbt_stream_h = $create_transaction_stream( {"..",get_full_name(),".","sbt_trans"} );
		end
	endtask : run

endclass : rsv_region_recorder

task rsv_region_recorder::print_record_trans(rsv_simop_trans tr);
	
	// This task visualize the simop transactions and records them in ModelSim.
	// You can use "add wave" command to view them on the waveform window. Please
	// refer to ModelSim User Manual for details.
	// 
	// The default implementation records all incomming transactions if the
	// "tr.sensitivity_level" is not OVM_FULL. Users can overide this behavior 
	// by deriving a new class.
	
	`print_info("ReSim", tr.conv2str(), tr.sensitivity_level);
	
	if (is_record_trans && (tr.sensitivity_level != OVM_FULL)) begin
		integer this_trans_h = 0;
		
		if (tr.op == SYNC) begin
			`check_fatal(sbt_trans_h == 0, "SBT_ERROR: @SYNC, simop transaction stream should not exist");
			sbt_trans_h = $begin_transaction(sbt_stream_h, "PARTIAL_RECONFIGURATION", tr.event_time);
		end

		`check_fatal(sbt_trans_h != 0, "SBT_ERROR: @PARTIAL_RECONFIGURATION, simop transaction stream should exist");

		this_trans_h = $begin_transaction(sbt_stream_h, $psprintf("%s",tr.op), tr.event_time, sbt_trans_h);
		$add_attribute(this_trans_h, tr.conv2str(), "OP");
		$end_transaction(this_trans_h, $realtime, 1);

		if (tr.op == DESYNC) begin
			`check_fatal(sbt_trans_h != 0, "SBT_ERROR: @DESYNC, simop transaction stream should exist");
			$end_transaction(sbt_trans_h, $realtime, 1); sbt_trans_h = 0;
		end
	end

endtask : print_record_trans

`endif // RSV_REGION_RECORDER_SVH
