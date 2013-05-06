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

`ifndef RSV_CONFIGURATION_PORT_SVH
`define RSV_CONFIGURATION_PORT_SVH

`include "rsv_icap_virtex.svh"
`include "rsv_sbt_parser.svh"

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_configuration_port#(int NUM_RR = 1) extends rsv_configuration_port_base#(NUM_RR);

	//---------------------------------------------------------------------
	// port, channel & sub-components
	//---------------------------------------------------------------------
	
	rsv_configuration_interface_base ci;
	rsv_configuration_parser_base#(NUM_RR) cc;

	tlm_fifo #(rsv_cdata_trans) cdata_fifo; // ICAP <-> SBT Parser
	
	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	`ovm_component_param_utils_begin(rsv_configuration_port#(NUM_RR))
	`ovm_component_utils_end

	//---------------------------------------------------------------------
	// constructor, build(), connect() & other ovm phase(s)
	//---------------------------------------------------------------------
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
		cdata_fifo = new("cdata_fifo", this);
	endfunction : new

	virtual function void build();
		super.build();

		ci  = rsv_configuration_interface_base::type_id::create("ci", this);
		cc  = rsv_configuration_parser_base#(NUM_RR)::type_id::create("cc", this);
	endfunction : build

	virtual function void connect();
		super.connect();

		ci.put_p.connect(cdata_fifo.put_export);
		cc.get_p.connect(cdata_fifo.get_peek_export);
		
		for (int i=0; i < NUM_RR; i++) begin
			cc.put_p[i].connect(put_p[i]);
		end
		

	endfunction : connect
	
	//---------------------------------------------------------------------
	// run()
	//---------------------------------------------------------------------
	
	// The run task does nothing
	
	virtual task run();
	endtask : run

endclass : rsv_configuration_port

`endif // RSV_CONFIGURATION_PORT_SVH
