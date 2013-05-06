#*******************************************************************************
# Copyright (c) 2012, Lingkan Gong
# All rights reserved.
# 
# Redistribution and use in source and binary forms, with or without 
# modification, are permitted provided that the following conditions are met:
# 
#  * Redistributions of source code must retain the above copyright notice, 
#    this list of conditions and the following disclaimer.
#
#  * Redistributions in binary form must reproduce the above copyright notice, 
#    this list of conditions and the following disclaimer in the documentation 
#    and/or other materials provided with the distribution.
#
#  * Neither the name of the copyright holder(s) nor the names of its
#    contributor(s) may be used to endorse or promote products derived from this 
#    software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#*******************************************************************************

namespace eval ReSim {
	namespace export rsv_register_state_spy
	namespace export rsv_unregister_state_spy
}

proc ReSim::rsv_gen_label { rr_ rm_ } {
	return [regsub -all -- {[\./]} "${rr_}/${rm_}" {_}] 
}

proc ReSim::rsv_load_spy_buffer { rr_ rm_ } {
	set rr_ /[regsub -all -- {[\.]} "${rr_}" {/}]
	
	mem load -infile "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_fa.txt" -format hex -filltype value -fillradix hex -filldata 0 $rr_/rm_sif/fa;
	mem load -infile "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_name.txt" -format hex -filltype value -fillradix hex -filldata 0 $rr_/rm_sif/name;
	mem load -infile "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_offt.txt" -format hex -filltype value -fillradix hex -filldata 0 $rr_/rm_sif/offt;
	
}

proc ReSim::rsv_iei_hdl_state { rr_ rm_ {iei_sig_type "none"} {iei_mem_type "none"} } {
	set rr_ /[regsub -all -- {[\.]} "${rr_}" {/}]
	echo "\[RESIM-SKT\] Invoking iei thread: rsv_iei_hdl_state $rr_ $rm_ $iei_sig_type $iei_mem_type"
	
	# Internal Error Injection (IEI): 
	#
	# This function is called when a module is swapped out so as to deactivate
	# all HDL signals of the module
	#
	# 1. walk though all hdl signals in the module
	# 2. "force" all hdl signals with undefined xxx
	# 3. "catch" all possible failures (e.g., errors in "find")
	
	if { $iei_sig_type == "zero" } {
		set iei_sig_type "16#0"
	} elseif { $iei_sig_type == "x" } {
		set iei_sig_type "16#x" 
	} else {
		set iei_sig_type "none"
	}
	
	if { $iei_mem_type == "zero" } {
		set iei_mem_type "value"
	} elseif { $iei_mem_type == "rand" } {
		set iei_mem_type "rand"
	} else {
		set iei_mem_type "none"
	}
	
	if { $iei_sig_type != "none" } {
		foreach sig [find signals -recursive $rr_/$rm_/*] {
			
			## Forcing signals is dangerous. The simulator sometimes crashes if 
			## the target signal can not be forced. (ModelSim could have report an 
			## error if the force fails but unfortunately, the simulator crashes)
			##
			## Version 1. "force $sig $iei_sig_type 1ps -cancel 1ps" // ModelSim crashes.
			## Version 2. 
			##     catch { force -deposit $sig $iei_sig_type 1ps -cancel 1ps } msg
			##     if { $msg != "" } { catch { change $sig $iei_sig_type } msg }
			##     
			##     // ModelSim crashes because of the force command. 
			##     // Use "force -deposit" command to change VHDL signals & Verilog nets.
			##     // Use "change" command to change Verilog registers.
			## 
			## Version 3. 
			##     catch { change $sig $iei_sig_type } msg
			##
			##     // Very slow for large designs
			##     // The "change" command can only change Verilog registers.
			
			catch { change $sig $iei_sig_type } msg
			
			#### For debugging
			#### 
			#### if { $msg != "" } { puts "\[RESIM-SKT\] $msg ($sig)" }
		}
		
		## Version 4. 
		##     foreach sig [find signals -in $rr_/$rm_/*] {
		##          catch { force -deposit $sig $iei_sig_type } msg
		##     }
		##
		##     // Whether or not to inject to RM inputs?
		##     // "force -deposit x" may not be able to un-forced properly
		##     // 
		##     // WAR: the target signal can drive with "x" before driving some other values
		##     // However, it is too tricy to be introduced to users.
		
	}
	
	# 4-6. walk through and "force" all memory cells in the module
	
	if { $iei_mem_type != "none" } {
	
		set memory_list [split [mem list -r $rr_/$rm_/*] "\n"]
		set num_of_memory [expr [llength $memory_list] -1]
		for { set i 0 } { $i<$num_of_memory } { incr i } {
			
			## Sample Entry:
			##
			##     VHDL: /board/system/engine_0/engine_0/rm0/cch1_data_o [0:3] x 8 w
			##     Verilog: /testbench/dut/fir_0/rm0/X_reg [0:20] x 16 w
			catch {
				
				set this_memory [lindex $memory_list $i]
				set this_memory_name [lindex $this_memory 1]
				set this_memory_depth [lindex $this_memory 4]
				
				mem load -filltype $iei_mem_type -fillradix hex -filldata 0 $this_memory_name
			}
		}
	
	}

}

proc ReSim::rsv_gcapture_hdl_state { rr_ rm_ } {
	set rr_ /[regsub -all -- {[\.]} "${rr_}" {/}]
	echo "\[RESIM-SKT\] Invoking gcapture thread: rsv_gcapture_hdl_state $rr_ $rm_"
	
	# Copy the values from signals to state_if
	# 
	# 1. capture the hdl values and write to a buffering file (...._value.txt)
	# the buffering file uses ModelSim's memory format so that later it can be 
	# loaded to the state_if using the "mem load" command
	
	set f_value [open "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_value.txt" w+]
	set f_name [open "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_name.txt" r];
	
	while {[gets $f_name line] >= 0} {
		
		# skip if comment or if empty line
		if { [regexp {^\s*//} $line] } { continue; }
		if { [llength $line] == 0 } { continue; }
		
		# one line of signal name file: e.g. @0 "/path/to/signal"
		set id [lindex $line 0]
		set sig [lindex $line 1]
		set val [examine -radix hex $sig]
		
		puts $f_value "$id $val"; 
	}
	
	close $f_value;
	close $f_name;
	
	# 2. load the buffering file into the state_if ($rr_/rm_sif/value)
	
	mem load -infile "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_value.txt" -format hex -filltype value -fillradix hex -filldata 0 $rr_/rm_sif/value;
}

proc ReSim::rsv_grestore_hdl_state { rr_ rm_ } {
	set rr_ /[regsub -all -- {[\.]} "${rr_}" {/}]
	echo "\[RESIM-SKT\] Invoking grestore thread: rsv_grestore_hdl_state $rr_ $rm_"
	
	# Copy the values from state_if to signals
	# 
	# 1. "force" the hdl signals with the values in the state_if ($rr_/rm_sif/value),
	# 2. release the "force" after a while, and all registers will keep the forced value 
	# 3. "catch" all possible failures (e.g., errors in "find")
	
	set f_name [open "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_name.txt" r];
	set val_l [lindex [examine -radix hex $rr_/rm_sif/value] 0]
	
	while {[gets $f_name line] >= 0} {
		
		# skip if comment or if empty line
		if { [regexp {^\s*//} $line] } { continue; }
		if { [llength $line] == 0 } { continue; }
		
		# one line of signal name file: e.g. @0 "/path/to/signal"
		scan [lindex $line 0] "@%x" i
		set sig [lindex $line 1]
		set val [lindex $val_l $i]
		
		if { $sig != "" && $val != "" } {
			catch { force $sig 16#$val 1ps -cancel 1ps } 
		}
		
	}
	
	close $f_name;
}

proc ReSim::rsv_register_state_spy { rr_ rm_ ll_ sbt_ } {
	set rr_ /[regsub -all -- {[\.]} "${rr_}" {/}]
	echo "\[RESIM-SKT\] Registering Simulator Kernel Thread (SKT): ${rr_}/${rm_}"

	# Register a state spy for a reconfigurable module
	#
	# This function is called at the start of simulation to initialize state spy
	# related files and variables. 
	
	rsv_assert { [string equal [find instances $rr_/$rm_] ""] == 0 } \
		"\[ERROR\] Module (${rr_}/${rm_}) does not exists"
	rsv_assert { [string equal [find instances $rr_/rm_sif] ""] == 0 } \
		"\[ERROR\] Module (${rr_}/${rm_}) is not reconfigurable"
	rsv_assert { [file exists $ll_] == 1 } \
		"\[ERROR\] Logic allocation (ll) file $ll_ does not exist!!!"
	rsv_assert { [file exists $sbt_] == 1 } \
		"\[ERROR\] Simulation-only bitstream (sbt) file $sbt_ does not exist!!!"
	rsv_assert { [file exists [file rootname $sbt_]_cdata.txt] == 1 } \
		"\[ERROR\] Configuration data (_cdata.txt) file of $sbt_ does not exist!!!"
	
	# Parse the logic allocation file (ll)
	#
	# Read logic allocation information (frame_address, signal_name, word_offset 
	# etc) from sll files and buffer them into ReSim internal files. These internal 
	# files will later be used by the state spy during simulation. 

	set f [open "$ll_" r+]
	
	set f_fa [open "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_fa.txt" w+];
	puts $f_fa "// ==== Name: spy_[rsv_gen_label $rr_ $rm_]_fa.txt ";
	puts $f_fa "// ==== Time: [clock format [clock seconds] -format  {%H:%M:%S, %B %d, %Y}] ";
	
	set f_name [open "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_name.txt" w+];
	puts $f_name "// ==== Name: spy_[rsv_gen_label $rr_ $rm_]_name.txt ";
	puts $f_name "// ==== Time: [clock format [clock seconds] -format  {%H:%M:%S, %B %d, %Y}] ";
	
	set f_offt [open "./artifacts/spy/spy_[rsv_gen_label $rr_ $rm_]_offt.txt" w+];
	puts $f_offt "// ==== Name: spy_[rsv_gen_label $rr_ $rm_]_offt.txt ";
	puts $f_offt "// ==== Time: [clock format [clock seconds] -format  {%H:%M:%S, %B %d, %Y}] ";
	
	set id 0; set lnum 1;
	while {[gets $f line] >= 0} {
		
		# skip if comment or if empty line
		if { [regexp {^\s*//} $line] } { incr lnum; continue; }
		if { [llength $line] == 0 } { incr lnum; continue; }
		
		# one line of ll file: e.g. 0x3 4 32 signal_name
		rsv_assert { [llength $line] == 4 } \
			"\[ERROR\] In logic allocation file ($ll_ ::$lnum): Syntax error ($line)!!!"
			
		set fa [lindex $line 0];
		set bofft [lindex $line 1];
		set bw [lindex $line 2];
		set sig $rr_/$rm_/[lindex $line 3];
		
		rsv_assert { [string is integer $fa] == 1 } \
			"\[ERROR\] In logic allocation file ($ll_ ::$lnum): frame address ($fa) should be an integer!!!"
		rsv_assert { [string is integer $bofft] == 1 } \
			"\[ERROR\] In logic allocation file ($ll_ ::$lnum): bit offset ($bofft) should be an integer!!!"
		rsv_assert { $bofft >= 32 } \
			"\[ERROR\] In logic allocation file ($ll_ ::$lnum): bit offset ($bofft) should be larger than 31!!!"
		rsv_assert { [string is integer $bw] == 1 } \
			"\[ERROR\] In logic allocation file ($ll_ ::$lnum): bitwidth ($bw) should be an integer!!!"
		rsv_assert { [expr $bofft + $bw] <= 128 } \
			"\[ERROR\] In logic allocation file ($ll_ ::$lnum): Each frame can only hold 128 bits of signals!!!"
		rsv_assert { [string equal [find signals $sig] ""] == 0 } \
			"\[ERROR\] In logic allocation file ($ll_ ::$lnum): Module ${rr_}/${rm_} do not have HDL signal $sig!!!"
		
		puts $f_fa "[format @%x $id] [format %08x $fa]";
		puts $f_name "[format @%x $id] \"$sig\"";
		puts $f_offt "[format @%x $id] [format %04x%04x $bofft $bw]";
		
		incr id; incr lnum;
	}

	close $f
	close $f_fa
	close $f_name
	close $f_offt
	
	# Register a Simulator Kernel Thread (SKT) for the state spy. 
	#
	# The "when" clause is registered in the ModelSim kernel, such that it checks the condition
	# and triggers the body of "when" clause if the condition is meet. It is equivalent to 
	# a "always" block in Verilog or "process" in VHDL, except that SKT can access all signals
	# within a simulation run. 
	#
	# As it is in the kernel, it can not see the variables (e.g. $rr_ $rm_) defined here. 
	# so I have to substitute the variables with there actual value before registration. 
	
	set label_ [rsv_gen_label $rr_ $rm_]
	
	#### The Simulator Kernel Threads (SKT) is no longer used. The registeration and 
	#### unregisteration of SKTs is not so easy for non-expert users. For the current
	#### implementation of ReSim, SKTs are called by class-based artifacts instead
	#### of being registered in the Simulator. 
	####
	#### set when_iei_thread "when -fast -label l_iei$label_ \"${rr_}/${rm_}_sif/is_active == 0\" {
	#### 	ReSim::rsv_iei_hdl_state $rr_ $rm_
	#### }"
	#### set when_gcapture_thread "when -fast -label l_cap$label_ \"${rr_}/${rm_}_sif/gcapture == 1\" {
	#### 	ReSim::rsv_gcapture_hdl_state $rr_ $rm_
	#### }"
	#### set when_grestore_thread "when -fast -label l_res$label_ \"${rr_}/${rm_}_sif/grestore == 1\" {
	#### 	ReSim::rsv_grestore_hdl_state $rr_ $rm_ 
	#### }"
	#### 
	#### eval $when_iei_thread
	#### eval $when_gcapture_thread
	#### eval $when_grestore_thread
	
	# Initialize the spy memory of the state interface. 
	#
	# If the module to be registered is the default module (rm0) of a reconfigurable region
	# then load its state_if with the default configuration data
	
	if { [string equal $rm_ "rm0"] } {
		mem load -filltype value -fillradix hex -filldata 0 $rr_/rm_sif/mem;
		mem load -infile "[file rootname $sbt_]_cdata.txt" -format hex $rr_/rm_sif/mem;
	}
	
}

proc ReSim::rsv_unregister_state_spy { rr_ rm_ } {
	set rr_ /[regsub -all -- {[\.]} "${rr_}" {/}]
	echo "\[RESIM-SKT\] Un-registering Simulator Kernel Thread (SKT): ${rr_}/${rm_}"

	# Unregister the state spy of a reconfigurable module
	#
	# This function should be called at the end of simulation to clean up the simulator kernel
	# This step is required if the user has previously registered a state spy during simulation
	
	rsv_assert { [string equal [find instances $rr_/$rm_] ""] == 0 } \
		"\[ERROR\] Reconfigurable module (${rr_}/${rm_}) does not exists"
	rsv_assert { [string equal [find instances $rr_/rm_sif] ""] == 0 } \
		"\[ERROR\] Reconfigurable module (${rr_}/${rm_}) is not reconfigurable"
	
	set label_ [rsv_gen_label $rr_ $rm_]
	
	#### Unregister the state spy using the labels defined early
	#### 
	#### nowhen l_iei$label_
	#### nowhen l_cap$label_
	#### nowhen l_res$label_

}
