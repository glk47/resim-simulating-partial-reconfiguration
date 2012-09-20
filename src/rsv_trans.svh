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
 *    contributors may be used to endorse or promote products derived from this 
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

	virtual function string conv2str();
		$timeformat (-9, 3, "ns", 5);
		return {$psprintf("[%s @ %0t]", phase, event_time)};
	endfunction : conv2str;

	virtual function rsv_trans clone(); /* should not be called */
		rsv_trans tr = new(event_time, phase, sensitivity_level);
		return tr;
	endfunction : clone;
	
endclass

// User-defined reconfiguration transactions:
//
//    rsv_usr_trans: the base class
//    rsv_unload_trans: the transaction when an unloading operation is collected
//    rsv_activate_trans: the transaction when an activation operation is collected
//    rsv_ei_trans: the transaction to inject errors DURING reconfiguration

class rsv_usr_trans extends rsv_trans;
	string op;
	string msg;

	function new (realtime t_, string op_, string msg_, phase_t ph_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, ph_, sl_);
		op  = op_;
		msg = msg_;
	endfunction : new

	virtual function string conv2str();
		return {super.conv2str(), " ", "USR_OP::", op, ", ", msg};
	endfunction : conv2str

	virtual function rsv_trans clone();
		rsv_usr_trans tr = new(event_time, op, msg, phase, sensitivity_level);
		return tr;
	endfunction : clone;
	
endclass: rsv_usr_trans

class rsv_unload_trans extends rsv_usr_trans;

	function new(realtime t_, string msg_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, "Unloading", msg_, BEFORE_PH, sl_);
	endfunction : new

	virtual function string conv2str();
		return {super.conv2str()};
	endfunction : conv2str

	virtual function rsv_trans clone();
		rsv_unload_trans tr = new(event_time, msg, sensitivity_level);
		return tr;
	endfunction : clone;
endclass: rsv_unload_trans

class rsv_activate_trans extends rsv_usr_trans;

	function new(realtime t_, string msg_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, "Activating", msg_, AFTER_PH, sl_);
	endfunction : new

	virtual function string conv2str();
		return {super.conv2str()};
	endfunction : conv2str

	virtual function rsv_trans clone();
		rsv_activate_trans tr = new(event_time, msg, sensitivity_level);
		return tr;
	endfunction : clone;
endclass: rsv_activate_trans

class rsv_ei_trans extends rsv_usr_trans;

	function new(realtime t_, string msg_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, "ErrInjection", msg_, DURING_PH, sl_);
	endfunction : new

	virtual function string conv2str();
		return {super.conv2str()};
	endfunction : conv2str

	virtual function rsv_trans clone();
		rsv_ei_trans tr = new(event_time, msg, sensitivity_level);
		return tr;
	endfunction : clone;
endclass: rsv_ei_trans

// Simulation only bitstream (sbt) reconfiguration transactions:
//
//    rsv_usr_trans: the base class
//    rsv_cfg_trans: the transaction for reconfigure/readback bitstream
//        this transaction will be processed by the portal controller
//    rsv_spy_trans: the transaction for saving/restoring states
//        this transaction will be processed by the state spy

// operations of the simulation-only bitstream
typedef enum {
	SYNC, DESYNC, RCFG, WCFG, ENDCFG, RSPY, WSPY, ENDSPY, GCAPTURE, GRESTORE
} rsv_sbt_op_t;

class rsv_sbt_trans extends rsv_trans;
	rsv_sbt_op_t op;

	function new (realtime t_, rsv_sbt_op_t op_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, DURING_PH, sl_);
		op = op_;
	endfunction : new

	virtual function string conv2str();
		return {super.conv2str(), " ", $psprintf("SBT_OP::%s", op)};
	endfunction : conv2str

	virtual function rsv_trans clone();
		rsv_sbt_trans tr = new(event_time, op, sensitivity_level);
		return tr;
	endfunction : clone;
endclass: rsv_sbt_trans

class rsv_cfg_trans extends rsv_sbt_trans;

	logic [7:0] rrid;
	logic [7:0] rmid;
	string name;

	function new(realtime t_, logic [7:0] rr_, logic [7:0] rm_, rsv_sbt_op_t op_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, op_, sl_);

		`check_error((op_==WCFG) || (op_==RCFG) || (op_==ENDCFG),
			$psprintf("Wrong op(%s) in cfg_trans",op_))

		rrid = rr_; rmid = rm_;
	endfunction : new

	virtual function string conv2str();
		if ((op==RCFG) || (op==WCFG)) begin
			return {super.conv2str(), ", ", 
				$psprintf("rrid= 0x%02h, rmid= 0x%02h, module= %s", rrid, rmid, name)};
		end else begin
			return {super.conv2str(), ", ", $psprintf("rrid= 0x%02h", rrid)};
		end
	endfunction : conv2str

	virtual function rsv_trans clone();
		rsv_cfg_trans tr = new(event_time, rrid, rmid, op, sensitivity_level);
		tr.name = name;
		return tr;
	endfunction : clone;
endclass: rsv_cfg_trans

class rsv_spy_trans extends rsv_sbt_trans;

	logic [7:0] rrid;
	logic [7:0] rmid;
	logic [15:0] mna;
	logic [31:0] cdata;
	int unsigned wofft;
	bit reach_boundary = 0;

	function new(realtime t_, logic [7:0] rr_, logic [7:0] rm_, logic [15:0] a_, int unsigned w_, logic [31:0] d_, rsv_sbt_op_t op_, int unsigned sl_ = OVM_HIGH);
		super.new(t_, op_, sl_);

		`check_error((op_==RSPY) || (op_==WSPY) || (op_==ENDSPY) || (op_==GCAPTURE) || (op_==GRESTORE),
			$psprintf("Wrong op(%s) in spy_trans",op_))

		rrid = rr_; rmid = rm_; mna = a_; wofft = w_; cdata = d_;
	endfunction : new
	
	virtual function string conv2str();
		if ((op==RSPY) || (op==WSPY)) begin
			return {super.conv2str(), ", ", 
				$psprintf("rrid= 0x%02h, rmid= 0x%02h, mna= 0x%04h, wofft= 0x%01h, cdata= 0x%08h", rrid, rmid, mna, wofft, cdata)};
		end else begin
			return {super.conv2str(), ", ", $psprintf("rrid= 0x%02h", rrid)};
		end
	endfunction : conv2str

	virtual function rsv_trans clone();
		rsv_spy_trans tr = new(event_time, rrid, rmid, mna, wofft, cdata, op, sensitivity_level);
		tr.reach_boundary = reach_boundary;
		return tr;
	endfunction : clone;
endclass: rsv_spy_trans

// Raw configuration data (cdata) transactions:
//
//    rsv_usr_trans: the base class
//    rsv_cfg_trans: the transaction for reconfigure/readback bitstream
//        this transaction will be processed by the portal controller
//    rsv_spy_trans: the transaction for saving/restoring states
//        this transaction will be processed by the state spy

// operations of the raw configuration data
typedef enum {
	RSBT, WSBT
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
		return {super.conv2str(), " ", $psprintf("CDATA::0x%08x", cdata)};
	endfunction : conv2str

	virtual function rsv_trans clone();
		rsv_cdata_trans tr = new(event_time, op, cdata, sensitivity_level);
		return tr;
	endfunction : clone;
endclass: rsv_cdata_trans
