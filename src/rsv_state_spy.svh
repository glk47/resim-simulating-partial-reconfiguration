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

`ifndef RSV_STATE_SPY_SVH
`define RSV_STATE_SPY_SVH

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_state_spy#(type IF=virtual interface null_if) extends rsv_state_spy_base;

	//---------------------------------------------------------------------
	// virtual interface(s)
	//---------------------------------------------------------------------
	
	IF spy_vi;
	virtual function void register_if(IF spy_);
		spy_vi = spy_;
	endfunction : register_if

	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	protected int unsigned num_fr = 1;
	protected string rr_inst = "";
	`ovm_component_param_utils_begin(rsv_state_spy#(IF))
		`ovm_field_int(num_fr, OVM_ALL_ON)
		`ovm_field_string(rr_inst, OVM_ALL_ON)
	`ovm_component_utils_end

	//---------------------------------------------------------------------
	// constructor, build(), connect() & other ovm phase(s)
	//---------------------------------------------------------------------
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	// build
	virtual function void build();
		super.build();
		`get_config_interface(rsv_if_wrapper #(IF),"spy_tag",spy_vi)
	endfunction : build

	//---------------------------------------------------------------------
	// run(), member tasks & member variables
	//---------------------------------------------------------------------
	
	`define num_of_hdl_signals (16*num_fr)
	
	protected logic m_gCapRes_msk = 0; 
	protected chandle interp;
	
	extern virtual task save_restore_state(rsv_spy_trans tr);
	extern virtual protected task state_spy_read(rsv_spy_trans tr);
	extern virtual protected task state_spy_write(rsv_spy_trans tr);
	extern virtual protected task state_spy_gcapture(rsv_spy_trans tr);
	extern virtual protected task state_spy_grestore(rsv_spy_trans tr);
	extern virtual protected task state_spy_check_signature(rsv_spy_trans tr);
	
	virtual task run();
		interp = mti_Interp();
	endtask : run

endclass : rsv_state_spy

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

task rsv_state_spy::save_restore_state(rsv_spy_trans tr);
	
	// The save_restore_state task performs state saving/restoration operations 
	// according to the incomming transaction. 
	// 
	// State data are stored in the spy memory, which is connected to the state spy 
	// through the state_if. The spy memory operates as a normal memory upon read
	// and write. And it's content is synchronized with HDL signals of modules whenever 
	// a GCAPTURE/GRESTORE is recieved.
	
	case (tr.op)
		WSPY: begin state_spy_write(tr); end
		RSPY: begin state_spy_read(tr); end
		ENDCFG: begin state_spy_check_signature(tr); end
		GCAPTURE: begin if (m_gCapRes_msk==1'b0) state_spy_gcapture(tr); end
		GRESTORE: begin if (m_gCapRes_msk==1'b0) state_spy_grestore(tr); end
		default: begin /* Ignore other operations */ end
	endcase

endtask : rsv_state_spy::save_restore_state

task rsv_state_spy::state_spy_write(rsv_spy_trans tr);

	if (tr.rmid == 8'hff) begin /* write mask frames */
		
		`check_error(tr.mna==0, $psprintf("Minor-address(0x%0h) == 0x%0h",tr.mna,0))
		`check_error(tr.wofft<=4, $psprintf("Word-offset(0x%0h) <= 0x%0h",tr.wofft,4))

		if (tr.wofft == 3) begin
			m_gCapRes_msk = tr.cdata[13:13];
			tr.reach_boundary = 1'b1;
		end
		
	end else begin /* write normal frames */
		int unsigned index = (tr.mna<<2) + tr.wofft;
		static int cdata_change_reported = 0;
		
		`check_error(tr.mna<=num_fr, $psprintf("Minor-address(0x%0h) <= 0x%0h",tr.mna,num_fr))
		`check_error(tr.wofft<=4, $psprintf("Word-offset(0x%0h) <= 0x%0h",tr.wofft,4))
		
		if ((tr.wofft == 0) && (cdata_change_reported == 0)) begin 
			if(!(spy_vi.mem[index] == tr.cdata)) begin 
				cdata_change_reported = 1;
				`print_info("ReSim", $psprintf(
					"SBT_INFO: Start writing cdata ... @0x%0h, 0x%0h -> 0x%0h",
					index,tr.cdata,spy_vi.mem[index]),OVM_HIGH)
			end
			
		end
		spy_vi.mem[index] = tr.cdata;
		
		if ( (tr.mna == (num_fr-1)) && (tr.wofft == 3) ) begin
			cdata_change_reported = 0;
			tr.reach_boundary = 1'b1; 
		end
		
	end

endtask : rsv_state_spy::state_spy_write

task rsv_state_spy::state_spy_read(rsv_spy_trans tr);

	if (tr.rmid == 8'hff) begin /* read mask frames */
		
		`check_error(tr.mna==0, $psprintf("Minor-address(0x%0h) == 0x%0h",tr.mna,0))
		`check_error(tr.wofft<=4, $psprintf("Word-offset(0x%0h) <= 0x%0h",tr.wofft,4))

		tr.cdata = 32'h0;
		if (tr.wofft == 3) begin
			tr.cdata = 32'h0 | (m_gCapRes_msk << 13);
			tr.reach_boundary = 1'b1; 
		end
		
	end else begin /* read normal frames */
		
		`check_error(tr.mna<=num_fr, $psprintf("Minor-address(0x%0h) <= 0x%0h",tr.mna,num_fr))
		`check_error(tr.wofft<=4, $psprintf("Word-offset(0x%0h) <= 0x%0h",tr.wofft,4))
		
		tr.cdata = spy_vi.mem[(tr.mna<<2) + tr.wofft];
		if ( (tr.mna == (num_fr-1)) && (tr.wofft == 3) ) begin
			tr.reach_boundary = 1'b1; 
		end
		
	end

endtask : rsv_state_spy::state_spy_read

task rsv_state_spy::state_spy_gcapture(rsv_spy_trans tr);

	// Call the utilities in the SKT to load logic allocation information (signal names, 
	// frame addresses, offsets in the .sll files) to state_if. Some delay is added 
	// to avoid clock edge. 
	
	#0.001;
	`rsv_execute_tcl(interp, $psprintf("ReSim::rsv_load_spy_buffer %s rm%0d",rr_inst,spy_vi.active_module_id))
	
	// Call the utilities in the SKT to perform GCAPTURE. The SKT reads values (using 
	// the ModelSim "examin" command) from the HDL signals listed in the .sll file 

	#0.001;
	`rsv_execute_tcl(interp, $psprintf("ReSim::rsv_gcapture_hdl_state %s rm%0d",rr_inst,spy_vi.active_module_id))

	// Assembly the configuration data according to the HDL signal values: The state 
	// spy reads the logic allocation information from the state_if, and use them to 
	// assembly the configuration data in the spy memory. 
	// 
	// note: spy memory start from bit offset = 32, word offset = 1, in the state_if,
	// note: each frame has 3*32=96bit storage

	for (int i=0; i < `num_of_hdl_signals; i++ ) begin
		if (spy_vi.name[i] != "0") begin // The unused entries are filled with "0" by ReSim::rsv_load_spy_buffer
			
			logic [31:0] fa    = spy_vi.fa[i];
			logic [31:0] offt  = spy_vi.offt[i];
			
			int unsigned rrid  = fa[31:24];
			int unsigned rmid  = fa[23:16];
			int unsigned mna   = fa[15:0];
			int unsigned bofft = offt[31:16]-32;
			int unsigned bw    = offt[15:0];

			logic [95:0] mem_mask;
			logic [95:0] mem_data;
			
			`check_error(tr.rrid==rrid, 
				$psprintf("RRid=0x%0h, RRid(expected)==0x%0h",tr.rrid,rrid))

			mem_mask = 96'b0; 
			for (int j=0; j< bw; j++ ) begin 
				mem_mask |= 1'b1 << (bofft+j); 
			end
			
			mem_data = ({spy_vi.mem[(mna<<2)+3], 
				spy_vi.mem[(mna<<2)+2], 
				spy_vi.mem[(mna<<2)+1]} & ~mem_mask) 
				| ((spy_vi.value[i]<<bofft) & mem_mask);
			
			spy_vi.mem[(mna<<2)+3] = mem_data[95:64];
			spy_vi.mem[(mna<<2)+2] = mem_data[63:32];
			spy_vi.mem[(mna<<2)+1] = mem_data[31:0];

		end
	end

endtask : rsv_state_spy::state_spy_gcapture

task rsv_state_spy::state_spy_grestore(rsv_spy_trans tr);
	
	// Call the utilities in the SKT to load logic allocation information (signal names, 
	// frame addresses, offsets in the .sll files) to state_if. Some delay is added 
	// to avoid clock edge. 
	
	#0.001;
	`rsv_execute_tcl(interp, $psprintf("ReSim::rsv_load_spy_buffer %s rm%0d",rr_inst,spy_vi.active_module_id))
	
	// Extract the signal values from the spy memory: The state spy reads 
	// the logic allocation information from the state_if, and use them to extract the 
	// signal values stored in the spy memory. 
	//
	// note: spy memory start from bit offset = 32, word offset = 1, in the state_if,
	// note: each frame has 3*32=96bit storage

	for (int i=0; i < `num_of_hdl_signals; i++ ) begin
		if (spy_vi.name[i] != "") begin
			
			logic [31:0] fa    = spy_vi.fa[i];
			logic [31:0] offt  = spy_vi.offt[i];
			
			int unsigned rrid  = fa[31:24];
			int unsigned rmid  = fa[23:16];
			int unsigned mna   = fa[15:0];
			int unsigned bofft = offt[31:16]-32;
			int unsigned bw    = offt[15:0];

			logic [95:0] mem_mask;
			logic [95:0] mem_data;
			
			`check_error(tr.rrid==rrid, 
				$psprintf("RRid=0x%0h, RRid(expected)==0x%0h",tr.rrid,rrid))

			mem_mask = 96'b0; 
			for (int j=0; j< bw; j++ ) begin 
				mem_mask |= 1'b1 << (bofft+j); 
			end
			
			mem_data = ({spy_vi.mem[(mna<<2)+3],
				spy_vi.mem[(mna<<2)+2],
				spy_vi.mem[(mna<<2)+1]} & mem_mask) >> bofft;

			spy_vi.value[i] = mem_data;

		end
	end

	// Call the utilities in the SKT to perform GRESTORE. The SKT writes values (using 
	// the ModelSim "force" command) to the HDL signals listed in the .sll file 

	#0.001;
	`rsv_execute_tcl(interp, $psprintf("ReSim::rsv_grestore_hdl_state %s rm%0d",rr_inst,spy_vi.active_module_id))

endtask : rsv_state_spy::state_spy_grestore

task rsv_state_spy::state_spy_check_signature(rsv_spy_trans tr);

	logic [31:0] sgnt = 32'h0; 
	for (int i = 0; i<num_fr; i++) begin 
		sgnt = sgnt ^ spy_vi.mem[i*4]; 
	end
	
	tr.cdata = sgnt;
	
	`check_error(sgnt==spy_vi.signature, 
		$psprintf("signature=0x%0h, signature(expected)=0x%0h",sgnt,spy_vi.signature))

endtask : rsv_state_spy::state_spy_check_signature
	
`endif // RSV_STATE_SPY_SVH
