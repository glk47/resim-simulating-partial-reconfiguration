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

`ifndef RSV_ICAP_VIRTEX_SVH
`define RSV_ICAP_VIRTEX_SVH

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_icap_virtex extends rsv_configuration_interface_base;

	//---------------------------------------------------------------------
	// virtual interface(s)
	//---------------------------------------------------------------------
	
	icap_if_type iif;
	virtual function void register_if(icap_if_type iif_);
		iif = iif_;
	endfunction : register_if

	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	`ovm_component_utils_begin(rsv_icap_virtex)
	`ovm_component_utils_end

	//---------------------------------------------------------------------
	// constructor, build(), connect() & other ovm phase(s)
	//---------------------------------------------------------------------
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	virtual function void build();
		super.build();
		`get_config_interface(rsv_if_wrapper #(icap_if_type),"iif_tag",iif)
	endfunction : build

	//---------------------------------------------------------------------
	// run(), member tasks & member variables
	//---------------------------------------------------------------------
	
	extern task rsv_cdata_thread();
	extern task rsv_readback_thread();
	extern task rsv_readback_busy_thread();
	
	// The run task manipulate the module-based part of the configuration port,
	// generates raw configuration data transactions, and sent them to the 
	// parser through the put port (put_p)

	virtual task run();
		fork
			rsv_cdata_thread();
			rsv_readback_thread();
			rsv_readback_busy_thread();
			
		join

	endtask : run
	
endclass : rsv_icap_virtex

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

task rsv_icap_virtex::rsv_cdata_thread();
	rsv_cdata_trans tr;

	forever begin
		@(posedge iif.cclk iff ((iif.ccs_n === 0) && (iif.cwe_n==1'b0) && (iif.cbusy==1'b0)));
		tr = new($realtime, WCDATA, iif.cdata);
		
		@(negedge iif.cclk); put_p.put(tr); @tr.done;
	end
	
endtask : rsv_icap_virtex::rsv_cdata_thread

task rsv_icap_virtex::rsv_readback_thread();
	rsv_cdata_trans tr;

	iif.cdata_rb <= 32'h0;
	forever begin
		@(posedge iif.cclk iff ((iif.ccs_n === 0) && (iif.cwe_n==1'b1) && (iif.cbusy==1'b0)));
		tr = new($realtime, RCDATA, 32'h0);
		
		@(negedge iif.cclk); put_p.put(tr); @tr.done;
		iif.cdata_rb <= tr.cdata;
	end
	
endtask : rsv_icap_virtex::rsv_readback_thread

task rsv_icap_virtex::rsv_readback_busy_thread();

	iif.cbusy <= 1'b1;
	forever begin
		@(negedge iif.ccs_n);
		
		if (iif.cwe_n==1'b1) begin /* Insert delay for configuration readback */
			repeat($urandom()%4) @(posedge iif.cclk);
		end
		iif.cbusy <= 1'b0;
		
		@(posedge iif.ccs_n);
		iif.cbusy <= 1'b1;
		
	end
	
endtask : rsv_icap_virtex::rsv_readback_busy_thread

`endif // RSV_ICAP_VIRTEX_SVH
