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

`timescale 1ns/1ps

interface null_if ();
	// Nothing in the null_if

endinterface: null_if

interface icap_if ();

	logic             cclk     ;       // icap: in  ---- user logic: out
	logic             ccs_n    ;       // icap: in  ---- user logic: out
	logic             cwe_n    ;       // icap: in  ---- user logic: out
	logic             cbusy    ;       // icap: out ---- user logic: in
	logic    [31:0]   cdata    ;       // icap: in  ---- user logic: out
	logic    [31:0]   cdata_rb ;       // icap: out ---- user logic: in

endinterface: icap_if

interface portal_if #(parameter NUM = 1)();

	// The portal_if of a reconfigurable region selects the CURRENT
	// active module and the CURRENT reconfiguration phase. 
	
	logic    [7:0]   active_module_id   ; // portal: out  ---- region: in
	logic            reconf_phase       ; // portal: out  ---- region: in
	
	// The portal_if also stores the names and signatures of 
	// all reconfigurable modules
	
	string           module_names[NUM]  ; // portal: in   ---- region: out
	logic    [31:0]  module_sgnts[NUM]  ; // portal: in   ---- region: out
	
endinterface: portal_if

interface error_if ();

	// The error_if is under the control of portal_if
	
	logic    [7:0]   active_module_id   ; // ei: in   ---- region: out
	logic            reconf_phase       ; // ei: in   ---- region: out

	// The error_if of a reconfigurable region enables or disables
	// the error injection operation.
	
	logic            sei_en          ; // ei: out ---- region: in (injecting io signals to the static region)
	logic            dei_en          ; // ei: out ---- region: in (injecting io signals to the dynamic region)

endinterface: error_if

interface state_if #(parameter NUM = 1)();
	
	// The state_if is under the control of portal_if
	
	logic    [7:0]   active_module_id   ; // spy: in   ---- region: out
	logic            reconf_phase       ; // spy: in   ---- region: out
	
	// Spy memory
	//
	// The state_if of a reconfigurable region is the place holder
	// for the spy memory, which stores the configuration data of the
	// CURRENT ACTIVE module.
	// 
	// In the spy memory, each RR has NUM frames and each frame has 4 32-bit words. Thus,
	//     word_address_in_spy_memory = frame_address*4 + word_offset.
	//
	// For one frame, the 0th word is to storage configuration data for "logic"
	// and word 1-3 is to store the "state data". state_if also hold a "signature"
	// field, which is the XORed value of all words with offset=0. This signature
	// is checked at the end of "DURING" reconfiguration phase. 

	logic    [31:0]  mem[4*NUM]  ;     // spy: in/out ---- region: in/out (configuration data)
	logic    [31:0]  signature   ;     // spy: in  ---- region: out

	// Spy buffer
	//
	// The spy buffer stores logic allocation information (fa, offset, etc)
	// specified in the .sll file. It is used to assembly the state data from
	// HDL signal values OR extract signal values from the state data.
	//
	// WAR: ReSim assumes that the average bitwidth of HDL signals are 8, thus 
	// each frame can store 16 signals. Users should allocate enough number of frames
	// so as to have enough space to store all HDL signals of interest.

	string           name[16*NUM] ;    // spy: in/out ---- SKT: in/out (hdl signal name)
	logic    [95:0]  value[16*NUM];    // spy: in/out ---- SKT: in/out (hdl signal value)
	logic    [31:0]  fa[16*NUM]   ;    // spy: in/out ---- SKT: in/out (hdl signal frame address)
	logic    [31:0]  offt[16*NUM] ;    // spy: in/out ---- SKT: in/out (hdl signal offset & bw in frame)

endinterface: state_if
