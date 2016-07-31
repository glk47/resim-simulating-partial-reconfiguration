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

`ifndef RSV_SCOREBOARD_SVH
`define RSV_SCOREBOARD_SVH

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_scoreboard#(int NUM_RR = 1) extends rsv_scoreboard_base#(NUM_RR);

	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	`ovm_component_param_utils_begin(rsv_scoreboard#(NUM_RR))
	`ovm_component_utils_end

	int has_reported_default_class_warning = 0;

	//---------------------------------------------------------------------
	// constructor, build(), connect() & other ovm phase(s)
	//---------------------------------------------------------------------
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	//---------------------------------------------------------------------
	// run()
	//---------------------------------------------------------------------
	
	// The run task get transaction (from the analysis fifo) and performs coverage
	// analysis according to the information exctracted from the transaction

	virtual task run();
		rsv_simop_trans tr;
		
		initialize_coverage();
		
		forever begin
			get_p.get(tr);
			collect_coverage(tr);
		end
	endtask : run

	virtual protected task initialize_coverage();
		if (!has_reported_default_class_warning) begin
			has_reported_default_class_warning = 1;
			`ovm_warning("ReSim", "Using the default scoreboard")
		end
	endtask : initialize_coverage
	
	virtual protected task collect_coverage(rsv_simop_trans tr);
		begin end
	endtask : collect_coverage

endclass : rsv_scoreboard

`endif // RSV_SCOREBOARD_SVH
