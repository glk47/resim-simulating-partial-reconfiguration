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

`ifndef RSV_IFS_WRAPPER_SVH
`define RSV_IFS_WRAPPER_SVH

// The rsv_if_wrapper class is a wrapper for the virtual interfaces. Using virual 
// interfaces and their wrappers, ReSim is de-coupled from the user-design, and 
// can be flexibly adapted to various design styles. 
//
// In particular, we store the interface warppers in the configuration table of 
// ReSim artifacts (note, we need a wrapper class because only objects can be 
// configured). The user-defined test code creates wrapper classes of user-defined 
// interfaces and pass the wrappers to the artifacts. The class-based artifacts 
// then retrieve the interfaces from the wrapper (using the get_if() member function) 
// and use such interface to access the signals of the module-based user design. 
// 
// In this way, virtual/actual interfaces are the boundary between the 
// artifacts with the user-design, i.e., ReSim is de-coupled from the user-design.

class rsv_if_wrapper#(type IF=virtual interface null_if) extends ovm_object;

	IF vi;

	function new (string nm_, IF vi_);
		super.new(nm_);
		set_if(vi_);
	endfunction

	virtual function IF get_if();
		return vi;
	endfunction

	virtual function void set_if(IF vi_);
		vi = vi_;
	endfunction

endclass : rsv_if_wrapper

`endif
