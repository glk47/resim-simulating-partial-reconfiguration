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

`ifndef RSV_TRANS_SVH
`define RSV_TRANS_SVH

// All possible phases of reconfiguration transition

typedef enum {
	NORMAL_PH, BEFORE_PH, DURING_PH, AFTER_PH
} phase_t;

// The base class for all reconfiguration transactions
// This is a virtual class and it can not be instantiated

virtual class rsv_trans;
	realtime event_time;
	phase_t  phase;
	int unsigned sensitivity_level = OVM_HIGH;
	
	event    done;

	function new (realtime t_,  phase_t ph_, int unsigned sl_ = OVM_HIGH);
		event_time = t_;
		phase = ph_;
		sensitivity_level = sl_;
	endfunction : new

endclass

// Simulation only bitstream (sbt) reconfiguration transactions:
//
//    rsv_simop_trans: The base class
//    rsv_cfg_trans: The transaction indicating the start and end of reconfiguration.
//        If it is a start, it also indicate whether it is to reconfigure or readback.
//        This transaction is created by sbt parser and is processed by the portal controller. 
//    rsv_ei_trans: The transaction indicating the start and end of error injection.
//        This transaction is created by sbt parser and is processed by the error injector
//    rsv_spy_trans: The transaction containing configuration(spy) memory content.
//        This transaction is created by sbt parser and is processed by the state spy

// operations of the simulation-only bitstream
typedef enum {
	SYNC, DESYNC, RCFG, WCFG, RSPY, WSPY, ENDCFG, GCAPTURE, GRESTORE
} rsv_sim_op_t;

class rsv_simop_trans extends rsv_trans;

	logic [7:0] rrid;
	logic [7:0] rmid;
	
	rsv_sim_op_t op;

	function new (realtime t_, logic [7:0] rr_, logic [7:0] rm_, rsv_sim_op_t op_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, DURING_PH, sl_);
		op = op_;
		rrid = rr_; rmid = rm_;
	endfunction : new
	
	virtual function string conv2str();
		if (rmid!=8'hff) begin
			return $psprintf("[SBT_OP::%s @ %s] rrid= 0x%02h, rmid= 0x%02h", op, phase, rrid, rmid);
		end else begin
			return $psprintf("[SBT_OP::%s @ %s] rrid= 0x%02h", op, phase, rrid);
		end
	endfunction : conv2str

	virtual function rsv_simop_trans clone();
		rsv_simop_trans tr = new(event_time, rrid, rmid, op, sensitivity_level);
		return tr;
	endfunction : clone;
endclass: rsv_simop_trans

class rsv_cfg_trans extends rsv_simop_trans;

	string name;

	function new(realtime t_, logic [7:0] rr_, logic [7:0] rm_, rsv_sim_op_t op_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, rr_, rm_, op_, sl_);

		`check_error((op_==WCFG) || (op_==RCFG) || (op_==ENDCFG),
			$psprintf("SBT_ERROR: Wrong op(%s) in cfg_trans",op_))

	endfunction : new

	virtual function string conv2str();
		if ((op==RCFG) || (op==WCFG)) begin
			return $psprintf("%s, module= %s", super.conv2str(), name);
		end else begin
			return $psprintf("%s (PC)",super.conv2str());
		end
	endfunction : conv2str

	virtual function rsv_simop_trans clone();
		rsv_cfg_trans tr = new(event_time, rrid, rmid, op, sensitivity_level);
		tr.name = name;
		return tr;
	endfunction : clone;
endclass: rsv_cfg_trans

class rsv_ei_trans extends rsv_simop_trans;
	
	string error_msg;
	
	function new(realtime t_, logic [7:0] rr_, logic [7:0] rm_, rsv_sim_op_t op_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, rr_, rm_, op_, sl_);

		`check_error((op_==WCFG) || (op_==RCFG) || (op_==ENDCFG),
			$psprintf("SBT_ERROR: Wrong op(%s) in ei_trans",op_))
		
		error_msg = "";
	endfunction : new

	virtual function string conv2str();
		if ((op==RCFG) || (op==WCFG)) begin
			return $psprintf("%s, error_msg= %s", super.conv2str(), error_msg);
		end else begin
			return $psprintf("%s (EI)",super.conv2str());
		end
	endfunction : conv2str

	virtual function rsv_simop_trans clone();
		rsv_ei_trans tr = new(event_time, rrid, rmid, op, sensitivity_level);
		tr.error_msg = error_msg;
		return tr;
	endfunction : clone;
endclass: rsv_ei_trans

class rsv_spy_trans extends rsv_simop_trans;

	logic [15:0] mna;
	logic [31:0] cdata;
	int unsigned wofft;
	bit reach_boundary = 0;

	function new(realtime t_, logic [7:0] rr_, logic [7:0] rm_, logic [15:0] a_, int unsigned w_, logic [31:0] d_, 
		rsv_sim_op_t op_, int unsigned sl_ = OVM_HIGH
	);
		super.new(t_, rr_, rm_, op_, sl_);

		`check_error((op_==RSPY) || (op_==WSPY) || (op_==ENDCFG) || (op_==GCAPTURE) || (op_==GRESTORE),
			$psprintf("SBT_ERROR: Wrong op(%s) in spy_trans",op_))

		mna = a_; wofft = w_; cdata = d_;
	endfunction : new
	
	virtual function string conv2str();
		if ((op==RSPY) || (op==WSPY)) begin
			return $psprintf("%s, mna= 0x%04h, wofft= 0x%01h, cdata= 0x%08h",super.conv2str(),mna,wofft,cdata);
		end else begin
			return $psprintf("%s (SPY)",super.conv2str());
		end
	endfunction : conv2str

	virtual function rsv_simop_trans clone();
		rsv_spy_trans tr = new(event_time, rrid, rmid, mna, wofft, cdata, op, sensitivity_level);
		tr.reach_boundary = reach_boundary;
		return tr;
	endfunction : clone;
endclass: rsv_spy_trans

// Raw configuration data (cdata) transactions:
//
//    rsv_cdata_trans: The transaction for raw bitstream configuration data.
//        This transaction is created by icapi driver and is processed by the sbt parser

// operations of the raw configuration data
typedef enum {
	RCDATA, WCDATA
} rsv_cdata_op_t;

class rsv_cdata_trans extends rsv_trans;
	logic[31:0] cdata;
	rsv_cdata_op_t op;

	function new (realtime t_, rsv_cdata_op_t op_, logic[31:0] d_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, DURING_PH, sl_);
		op = op_;
		cdata = d_;
	endfunction : new
	
	virtual function string conv2str();
		return $psprintf("[CDATA @ %s] cdata=0x%08x", phase, cdata);
	endfunction : conv2str

	virtual function rsv_cdata_trans clone();
		rsv_cdata_trans tr = new(event_time, op, cdata, sensitivity_level);
		return tr;
	endfunction : clone;
endclass: rsv_cdata_trans

`endif
