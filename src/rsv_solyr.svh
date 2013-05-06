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

`ifndef RSV_SOLYR_SVH
`define RSV_SOLYR_SVH

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_solyr#(int NUM_RR = 1) extends ovm_env;

	//---------------------------------------------------------------------
	// port, channel & sub-components
	//---------------------------------------------------------------------
	
	rsv_configuration_port_base#(NUM_RR) cp;
	rsv_region rr[NUM_RR];
	rsv_scoreboard_base#(NUM_RR) scb;
	
	tlm_fifo #(rsv_simop_trans) rr_fifo[NUM_RR];   // Configuration Port <-> Reconfigurable Region
	tlm_analysis_fifo #(rsv_simop_trans) scb_fifo; // Reconfigurable Region <-> Scoreboard
	
	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	`ovm_component_param_utils_begin(rsv_solyr#(NUM_RR))
	`ovm_component_utils_end

	//---------------------------------------------------------------------
	// constructor, build(), connect() & other ovm phase(s)
	//---------------------------------------------------------------------
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
		
		for (int i=0; i < NUM_RR; i++) begin
			rr_fifo[i]  = new($psprintf("rr_fifo_%0d", i), this);
		end
		scb_fifo = new("scb_fifo", this);
		
	endfunction : new

	virtual function void build();
		super.build();

		cp  = rsv_configuration_port_base#(NUM_RR)::type_id::create("cp", this);
		for (int i=0; i < NUM_RR; i++) begin
			rr[i] = rsv_region::type_id::create($psprintf("rr%0d", i), this);
		end
		scb = rsv_scoreboard_base#(NUM_RR)::type_id::create("scb", this);

	endfunction : build

	virtual function void connect();
		super.connect();
		
		for (int i=0; i < NUM_RR; i++) begin
			cp.put_p[i].connect(rr_fifo[i].put_export);
			rr[i].get_p.connect(rr_fifo[i].get_peek_export);
			rr[i].ap.connect(scb_fifo.analysis_export);
		end
		
		scb.get_p.connect(scb_fifo.get_peek_export);

	endfunction : connect

endclass : rsv_solyr

`endif // RSV_SOLYR_SVH
