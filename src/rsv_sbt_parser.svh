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

`ifndef RSV_SBT_PARSER_SVH
`define RSV_SBT_PARSER_SVH

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

class rsv_sbt_parser#(int NUM_RR = 1) extends rsv_configuration_parser_base#(NUM_RR);

	//---------------------------------------------------------------------
	// virtual interface(s)
	//---------------------------------------------------------------------
	// none 
	
	//---------------------------------------------------------------------
	// configuration table and parameter(s)
	//---------------------------------------------------------------------
	
	`ovm_component_param_utils_begin(rsv_sbt_parser#(NUM_RR))
	`ovm_component_utils_end

	//---------------------------------------------------------------------
	// constructor, build(), connect() & other ovm phase(s)
	//---------------------------------------------------------------------
	
	function new (string name, ovm_component parent);
		super.new(name, parent);
	endfunction : new

	virtual function void build();
		super.build();
	endfunction : build

	//---------------------------------------------------------------------
	// run(), member tasks & member variables
	//---------------------------------------------------------------------
	
	const logic [2:0] IOP_NOP = 2'h0;
	const logic [2:0] IOP_RD  = 2'h1;
	const logic [2:0] IOP_WR  = 2'h2;

	const logic [5:0] IREG_CRC  = 5'h0;
	const logic [5:0] IREG_CMD  = 5'h4;
	const logic [5:0] IREG_STAT = 5'h7;
	const logic [5:0] IREG_FAR  = 5'h1;
	const logic [5:0] IREG_FDRI = 5'h2;
	const logic [5:0] IREG_FDRO = 5'h3;
	const logic [5:0] IREG_ID   = 5'hc;

	const logic [4:0] ICMD_NULL     = 4'h0;
	const logic [4:0] ICMD_WCFG     = 4'h1;
	const logic [4:0] ICMD_RCFG     = 4'h4;
	const logic [4:0] ICMD_RCRC     = 4'h7;
	const logic [4:0] ICMD_GRESTORE = 4'ha;
	const logic [4:0] ICMD_GCAPTURE = 4'hc;
	const logic [4:0] ICMD_DESYNC   = 4'hd;

	`define sbt_type(sbt_)     sbt_[31:29]
	`define sbt_t1h_op(sbt_)   sbt_[28:27]
	`define sbt_t1h_addr(sbt_) sbt_[17:13]
	`define sbt_t1h_wc(sbt_)   sbt_[10:0]
	`define sbt_t2h_wc(sbt_)   sbt_[26:0]
	
	protected logic [31:0] m_regs[32]; // configuration registers

	protected bit m_is_sync = 0;
	protected int unsigned m_sbt_op;
	protected int unsigned m_sbt_wc;
	protected int unsigned m_sbt_addr;
	protected realtime m_t12h_time;

	extern protected task icap_process_packet_header();
	extern protected task icap_process_1_packet_data();
	extern protected task icap_process_n_packet_data();

	extern protected task icap_wr_cmd(realtime t);
	extern protected task icap_wr_fdri(realtime t, int unsigned i, logic [31:0] d_);
	extern protected task icap_rd_fdro(realtime t, int unsigned i, output logic [31:0] d_);
	
	extern protected task icap_start_of_configuration(realtime t);
	extern protected task icap_end_of_configuration(realtime t);
	
	extern protected task icap_cmd_sync(realtime t);
	extern protected task icap_cmd_dsync(realtime t);
	extern protected task icap_cmd_gcapture(realtime t);
	extern protected task icap_cmd_grestore(realtime t);
	
	// The run task converts raw cdata transactions from the configuration
	// port to high-level simop transactions to the reconfigurable regions
	// (RRs) through the put ports (put_p[])

	virtual task run();
		m_regs[IREG_ID] = 32'h0c1b2011; /* simulation-only device id */

		forever begin
			icap_process_packet_header();
			
			case (m_sbt_wc) 
				0: begin continue; end
				1: begin icap_process_1_packet_data(); end
				default: begin /* multiple data words */ 
					icap_process_n_packet_data();
				end
			endcase
			
			m_sbt_op = IOP_NOP;
			m_sbt_wc = 0;
			m_sbt_addr = 0;
		end
			
	endtask : run
	
endclass : rsv_sbt_parser

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

task rsv_sbt_parser::icap_process_packet_header();
	rsv_cdata_trans tr;
	
	get_p.get(tr);
	`check_error(tr.op==WCDATA, $psprintf("SBT_ERROR: Expecting Configuration SBT"))
	
	if ((m_is_sync == 0)||(tr.cdata == 32'haa995566)||(tr.cdata == 32'hffffffff)) begin
		m_sbt_wc = 0;
		if ((m_is_sync == 0) && (tr.cdata == 32'haa995566)) begin
			icap_cmd_sync(tr.event_time);
		end
	end else begin /* m_is_sync==1*/
	
		case (`sbt_type(tr.cdata))
			3'b001: begin /* Type 1 Header */
				m_sbt_op = `sbt_t1h_op(tr.cdata);
				m_sbt_wc = `sbt_t1h_wc(tr.cdata);
				m_sbt_addr = `sbt_t1h_addr(tr.cdata);
				m_t12h_time= tr.event_time;
			end
			3'b010: begin /* Type 2 Header */
				`check_error(m_sbt_wc==0, $psprintf("SBT_ERROR: Type 2 Header should have zero Word Count"))
				m_sbt_wc = `sbt_t2h_wc(tr.cdata);
			end
			default: begin /* Unexpected Header */
				`check_error(0,"SBT_ERROR: Unexpected SBT Header type")
				m_sbt_wc = 0;
			end
		endcase
		
	end

	-> tr.done;
	
endtask : rsv_sbt_parser::icap_process_packet_header

task rsv_sbt_parser::icap_process_1_packet_data();
	rsv_cdata_trans tr;
	
	// For single word packet, do not support reading/writing FDRI & FDRO
	// The single packet processing task can only be used to read/write ICAP cfg registers
	
	`check_error(!((m_sbt_addr==IREG_FDRI)||(m_sbt_addr== IREG_FDRO)),
		$psprintf("SBT_ERROR: Does not support 1 word packet for FDRI/FDRO"))
	
	// The ICAP artifact do not have pipeline. Each SBT word is directly parsed by the 
	// SBT_PARSER. Therefore, user can not insert unexpected NOP packets into the SBT. 

	get_p.get(tr);
	
	case (m_sbt_op)
		IOP_RD: begin 
			`check_error(tr.op==RCDATA, $psprintf("SBT_ERROR: Expecting Readback SBT"))
			tr.cdata=m_regs[m_sbt_addr];
		end
		IOP_WR: begin 
			`check_error(tr.op==WCDATA, $psprintf("SBT_ERROR: Expecting Configuration SBT"))
			m_regs[m_sbt_addr] = tr.cdata;
			if (m_sbt_addr == IREG_CMD) icap_wr_cmd(m_t12h_time);
		end
		default: begin /* IOP_NOP, IOP_RESERVED */ `check_error(0,"") end
	endcase
	
	-> tr.done;

endtask : rsv_sbt_parser::icap_process_1_packet_data

task rsv_sbt_parser::icap_process_n_packet_data();
	rsv_cdata_trans tr;

	// For multiple word packet data, only support FDRI & FDRO
	// This multiple packet processing task can only be used for 
	// writing/reading configuration data
	
	`check_error((m_sbt_addr==IREG_FDRI)||(m_sbt_addr== IREG_FDRO),
		$psprintf("SBT_ERROR: only support multiple words packet for FDRI/FDRO"))
	
	// Start reading/writing the configuration memory
	
	icap_start_of_configuration(m_t12h_time);

	for (int i=0; i < m_sbt_wc; i++ ) begin
		
		get_p.get(tr);
		
		case (m_sbt_op)
			IOP_RD: begin
				`check_error(tr.op==RCDATA, $psprintf("SBT_ERROR: Expecting Readback SBT"))
				case (m_sbt_addr) 
					IREG_FDRO: begin icap_rd_fdro(tr.event_time,i,tr.cdata); end
					default: begin /* Read FDRI */ end
				endcase
			end
			IOP_WR: begin
				`check_error(tr.op==WCDATA, $psprintf("SBT_ERROR: Expecting Configuration SBT"))
				case (m_sbt_addr) 
					IREG_FDRI: begin icap_wr_fdri(tr.event_time,i,tr.cdata); end
					default: begin /* Write FDRO */ end
				endcase
			end
			default: begin /* IOP_NOP, IOP_RESERVED */ `check_error(0,"") end
		endcase
		
		-> tr.done;
	end
	
	// End reading/writing the configuration memory
	
	icap_end_of_configuration($realtime);

endtask : rsv_sbt_parser::icap_process_n_packet_data

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

task rsv_sbt_parser::icap_wr_cmd(realtime t);
	case (m_regs[IREG_CMD][4:0]) 
		ICMD_NULL: begin end
		ICMD_RCRC: begin m_regs[IREG_CRC] = 32'h0; end
		ICMD_WCFG: begin /* WCFG starts when writing the configuration data */ end
		ICMD_RCFG: begin /* RCFG starts when reading the configuration data */ end
		ICMD_GRESTORE: begin icap_cmd_grestore(t); end
		ICMD_GCAPTURE: begin icap_cmd_gcapture(t); end
		ICMD_DESYNC: begin icap_cmd_dsync(t); end
		default: begin /* OTHER Commands */ end
	endcase

endtask : rsv_sbt_parser::icap_wr_cmd

task rsv_sbt_parser::icap_wr_fdri(realtime t, int unsigned i, logic [31:0] d_);

	// This task writes configuration data to the configuration memroy.
	// It sends WSPY transactions to the targe RR.
	
	logic [7:0] rrid = m_regs[IREG_FAR][31:24];
	logic [7:0] rmid = m_regs[IREG_FAR][23:16];
	logic [15:0] mna = m_regs[IREG_FAR][15:0];
	int unsigned wofft = i % 4; 
	rsv_spy_trans tr = new(t, rrid, rmid, mna, wofft, d_, WSPY);
	
	`check_error(rrid<=NUM_RR, $psprintf("SBT_ERROR: RRid(0x%0h) <= 0x%0h",rrid,NUM_RR))
	
	put_p[rrid].put(tr); @tr.done;
	
	// When done, check whether the frame address has reached the boundary of 
	// the current reconfigurable region (tr.reach_boundary == 1'b1).
	// ReSim do not wrap the rrid to the next region. In general, the frame 
	// are not continuous across RRs.
	
	if (tr.reach_boundary) begin
		`print_info("ReSim", "SBT_INFO: End of current Reconfigurable Region", OVM_HIGH)
		m_regs[IREG_FAR][15:0] = 16'h0;
	end else begin
		if (tr.wofft == 3)
			m_regs[IREG_FAR][15:0]++;
	end

endtask : rsv_sbt_parser::icap_wr_fdri

task rsv_sbt_parser::icap_rd_fdro(realtime t, int unsigned i, output logic [31:0] d_);

	// This task reads configuration data from the configuration memroy.
	// It sends RSPY transactions to the targe RR.
	
	logic [7:0] rrid = m_regs[IREG_FAR][31:24];
	logic [7:0] rmid = m_regs[IREG_FAR][23:16];
	logic [15:0] mna = m_regs[IREG_FAR][15:0];
	int unsigned wofft = i % 4; 
	rsv_spy_trans tr = new(t, rrid, rmid, mna, wofft, 0, RSPY);
	
	`check_error(rrid<=NUM_RR, $psprintf("SBT_ERROR: RRid(0x%0h) <= 0x%0h",rrid,NUM_RR))
	
	put_p[rrid].put(tr); @tr.done; d_ = tr.cdata;
	
	// When done, check whether the frame address has reached the boundary of 
	// the current reconfigurable region (tr.reach_boundary == 1'b1).
	// ReSim do not wrap the rrid to the next region. In general, the frame 
	// are not continuous across RRs.
	
	if (tr.reach_boundary) begin
		`print_info("ReSim", "SBT_INFO: End of current Reconfigurable Region", OVM_HIGH)
		m_regs[IREG_FAR][15:0] = 16'h0;
	end else begin
		if (tr.wofft == 3)
			m_regs[IREG_FAR][15:0]++;
	end

endtask : rsv_sbt_parser::icap_rd_fdro

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

task rsv_sbt_parser::icap_cmd_sync(realtime t);

	for (int i = 0; i<NUM_RR; i++) begin
		rsv_simop_trans tr = new(t, i, 8'hff, SYNC);
		put_p[i].put(tr);
	end
	m_is_sync = 1; 

endtask : rsv_sbt_parser::icap_cmd_sync

task rsv_sbt_parser::icap_cmd_dsync(realtime t);
	
	for (int i = 0; i<NUM_RR; i++) begin
		rsv_simop_trans tr = new(t, i, 8'hff, DESYNC);
		put_p[i].put(tr);
	end
	m_is_sync = 0; 

endtask : rsv_sbt_parser::icap_cmd_dsync

task rsv_sbt_parser::icap_start_of_configuration(realtime t);

	// This task represents the start of "DURING phase" of a reconfiguration
	// process. In ReSim, it informs (1) the portal controller to perform
	// module swapping and, (2) the error injector to start error injection. 
	
	logic [7:0] rrid = m_regs[IREG_FAR][31:24];
	logic [7:0] rmid = m_regs[IREG_FAR][23:16];
	logic [15:0] mna = m_regs[IREG_FAR][15:0];
	rsv_cfg_trans tr_0;
	rsv_ei_trans tr_1;
	
	`check_error(rrid<=NUM_RR, $psprintf("RRid(0x%0h) <= 0x%0h",rrid,NUM_RR))
	
	case (m_sbt_op)
		IOP_RD: begin 
			`check_error(m_regs[IREG_CMD][4:0]==ICMD_RCFG,"")
			tr_0 = new(t, rrid, rmid, RCFG, OVM_MEDIUM);
			tr_1 = new(t, rrid, rmid, RCFG, OVM_FULL);
		end
		IOP_WR: begin 
			`check_error(m_regs[IREG_CMD][4:0]==ICMD_WCFG,"")
			tr_0 = new(t, rrid, rmid, WCFG, OVM_MEDIUM);
			tr_1 = new(t, rrid, rmid, WCFG, OVM_FULL);
		end
		default: begin /* IOP_NOP, IOP_RESERVED */ `check_error(0,"") end
	endcase
	
	// Push the transaction to the target RR and wait until done
	
	fork
		begin put_p[rrid].put(tr_0); @tr_0.done; end
		begin put_p[rrid].put(tr_1); @tr_1.done; end
	join
	
endtask : rsv_sbt_parser::icap_start_of_configuration
	
task rsv_sbt_parser::icap_end_of_configuration(realtime t);

	// This task represents end start of "DURING phase" of a reconfiguration
	// process. In ReSim, it informs (1) the portal controller to resume
	// normal connection, (2) the error injector to stop error injection and,
	// (3) the state spy to check module signature. 
	
	logic [7:0] rrid = m_regs[IREG_FAR][31:24];
	
	rsv_cfg_trans tr_0 = new(t, rrid, 8'hff, ENDCFG, OVM_FULL);
	rsv_ei_trans tr_1 = new(t, rrid, 8'hff, ENDCFG, OVM_FULL);
	rsv_spy_trans tr_2 = new(t, rrid, 8'hff, 0, 0, 0, ENDCFG, OVM_FULL);
	
	`check_error(rrid<=NUM_RR, $psprintf("RRid(0x%0h) <= 0x%0h",rrid,NUM_RR))
	
	// Push the transaction to the target RR and wait until done
	
	fork
		begin put_p[rrid].put(tr_0); @tr_0.done; end
		begin put_p[rrid].put(tr_1); @tr_1.done; end
		begin put_p[rrid].put(tr_2); @tr_2.done; end
	join
	
endtask : rsv_sbt_parser::icap_end_of_configuration

task rsv_sbt_parser::icap_cmd_gcapture(realtime t);

	for (int i = 0; i<NUM_RR; i++) begin 
		rsv_spy_trans tr = new(t, i, 8'hff, 0, 0, 0, GCAPTURE, OVM_MEDIUM);
		put_p[i].put(tr); @tr.done;
	end
	
endtask : rsv_sbt_parser::icap_cmd_gcapture

task rsv_sbt_parser::icap_cmd_grestore(realtime t);
	
	for (int i = 0; i<NUM_RR; i++) begin 
		rsv_spy_trans tr = new(t, i, 8'hff, 0, 0, 0, GRESTORE, OVM_MEDIUM);
		put_p[i].put(tr); @tr.done;
	end
	
endtask : rsv_sbt_parser::icap_cmd_grestore

`endif // RSV_SBT_PARSER_SVH
