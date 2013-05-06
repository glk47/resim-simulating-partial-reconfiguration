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

#############################################
## Data structure creation
#############################################

namespace eval ReSim {
	namespace export rsv_cleanup
	namespace export rsv_create_portmap
	namespace export rsv_add_port
	namespace export rsv_create_region
	namespace export rsv_add_module
	namespace export rsv_create_solyr
	namespace export rsv_add_region

	variable portmap_a
	variable region_a
	variable solyr_a
}

proc ReSim::rsv_cleanup { } {
	variable portmap_a
	variable region_a
	variable solyr_a
	variable mem_a
	
	array unset portmap_a
	array unset region_a
	array unset solyr_a
	array unset mem_a
}
proc ReSim::rsv_create_portmap { ri_ clk_ } {
	variable portmap_a
	
	rsv_assert { [llength [array names portmap_a -exact $ri_.nm]] == 0 } \
		"\[ERROR\] portmap $ri_ has already been created!!!"
		
	set portmap_a($ri_.nm) $ri_
	set portmap_a($ri_.pm) {}
	set portmap_a($ri_.clk) $clk_; if { $clk_ != "" } { rsv_add_port $ri_ $clk_ in }
}
proc ReSim::rsv_add_port { ri_ nm_ io_ {bw_ 1} } {
	variable portmap_a
	
	set my_port [list $nm_ $io_ $bw_]
	
	rsv_assert { [llength [array names portmap_a -exact $ri_.nm]] == 1 } \
		"\[ERROR\] portmap $ri_ should be created before adding ports!!!"
	foreach my_port_ $portmap_a($ri_.pm) { 
		rsv_assert { [string equal [lindex $my_port_ 0] [lindex $my_port 0]] == 0 } \
			"\[ERROR\] port $nm_ already exists in portmap $ri_!!!"
	}
	
	lappend portmap_a($ri_.pm) $my_port
}
proc ReSim::rsv_create_region { rr_ ri_ sz_ {rec_ ""} {ei_ ""} } {
	variable portmap_a
	variable region_a

	rsv_assert { [llength [array names region_a -exact $rr_.nm]] == 0 } \
		"\[ERROR\] region $rr_ has already been created!!!"
	rsv_assert { [llength [array names portmap_a -exact $ri_.nm]] == 1 } \
		"\[ERROR\] portmap $ri_ should be created before creating a region!!!"
		
	set region_a($rr_.nm) $rr_
	set region_a($rr_.ri) $ri_
	set region_a($rr_.sz) $sz_
	set region_a($rr_.rec) $rec_
	set region_a($rr_.ei) $ei_
	set region_a($rr_.rm) {}
}
proc ReSim::rsv_add_module { rr_ rm_ {gm_ ""} {bit_ ""} } {
	variable portmap_a
	variable region_a

	set my_module [list $rm_ $gm_ 0]
	
	rsv_assert { [llength [array names region_a -exact $rr_.nm]] == 1 } \
		"\[ERROR\] region $rr_ should be created before adding modules!!!"
	foreach my_module_ $region_a($rr_.rm) { 
		rsv_warning { [string equal [lindex $my_module_ 0] [lindex $my_module 0]] == 0 } \
			"\[WARNING\] module $rm_ already exists in region $rr_!!!"
	}
	
	lappend region_a($rr_.rm) $my_module
}
proc ReSim::rsv_create_solyr { vf_ {type_ VIRTEX4} {scb_ ""}} {
	variable region_a
	variable solyr_a

	rsv_assert { [llength [array names solyr_a -exact $vf_.nm]] == 0 } \
		"\[ERROR\] solyr $vf_ has already been created!!!"
	rsv_assert { [llength [array names solyr_a -glob *.nm]] == 0 } \
		"\[ERROR\] you can only create one solyr!!!"
	rsv_assert { [string equal $type_ VIRTEX4] == 1 || \
		[string equal $type_ VIRTEX5] == 1 || \
		[string equal $type_ VIRTEX6] == 1} \
		"\[ERROR\] wrong solyr type specified, only support VIRTEX4/5/6!!!"
		
	set solyr_a($vf_.nm) $vf_
	if { $type_ == "VIRTEX4" } { set solyr_a($vf_.cp) "ICAP_VIRTEX4_WRAPPER" }
	if { $type_ == "VIRTEX5" } { set solyr_a($vf_.cp) "ICAP_VIRTEX5_WRAPPER" }
	if { $type_ == "VIRTEX6" } { set solyr_a($vf_.cp) "ICAP_VIRTEX6_WRAPPER" }
	set solyr_a($vf_.rec) {}
	set solyr_a($vf_.ei) {}
	set solyr_a($vf_.scb) $scb_
	set solyr_a($vf_.ri) {}
	set solyr_a($vf_.rr) {}
}
proc ReSim::rsv_add_region { vf_ rr_ } {
	variable region_a
	variable solyr_a
	
	rsv_assert { [llength $region_a($rr_.rm)] > 0 && [llength $region_a($rr_.rm)] < 128 } \
		"\[ERROR\] Too many or too few modules in $rr_, should >=1 and <=127!!!"

	lappend solyr_a($vf_.rr) $rr_
}

#############################################
## Helper printers
#############################################

namespace eval ReSim {

	variable portmap_a
	variable region_a
	variable solyr_a
}

proc ReSim::rsv_print_license {} {
	set str "";

	append str "/*******************************************************************************   \n"
	append str " * Copyright (c) 2012, Lingkan Gong                                                \n"
	append str " * All rights reserved.                                                            \n"
	append str " *                                                                                 \n"
	append str " * Redistribution and use in source and binary forms, with or without              \n"
	append str " * modification, are permitted provided that the following conditions are met:     \n"
	append str " *                                                                                 \n"
	append str " *  * Redistributions of source code must retain the above copyright notice,       \n"
	append str " *    this list of conditions and the following disclaimer.                        \n"
	append str " *                                                                                 \n"
	append str " *  * Redistributions in binary form must reproduce the above copyright notice,    \n"
	append str " *    this list of conditions and the following disclaimer in the documentation    \n"
	append str " *    and/or other materials provided with the distribution.                       \n"
	append str " *                                                                                 \n"
	append str " *  * Neither the name of the copyright holder(s) nor the names of its             \n"
	append str " *    contributor(s) may be used to endorse or promote products derived from this  \n"
	append str " *    software without specific prior written permission.                          \n"
	append str " *                                                                                 \n"
	append str " * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS \"AS IS\" AND \n"
	append str " * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED   \n"
	append str " * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE          \n"
	append str " * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS BE LIABLE FOR ANY           \n"
	append str " * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES      \n"
	append str " * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;    \n"
	append str " * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     \n"
	append str " * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      \n"
	append str " * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS   \n"
	append str " * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                    \n"
	append str " *                                                                                 \n"
	append str "*******************************************************************************/   \n"

	return $str
}

proc ReSim::rsv_print_port_io { ri_ nm_ io_ bw_ i args } {
	if { $io_ == "in" } {set str "input "}
	if { $io_ == "out"} {set str "output"}
	if { $bw_ == 1 } { return [format "\t$str          %-16s" $nm_] }
	if { $bw_ != 1 } { return [format "\t$str  \[%2d:0\]  %-16s" [expr $bw_ - 1] $nm_] }
}
proc ReSim::rsv_print_port_inst { ri_ nm_ io_ bw_ i args } {
	return [format "\t\t.%-16s ( [lindex $args 0]%-16s )" $nm_ $nm_]
}
proc ReSim::rsv_print_port_cnct { ri_ nm_ io_ bw_ i args } {
	## TO BE REMOVED
	if { $io_ == "in" }  { return [format "\t\tdyn_rif.%-16s = sta_rif.%-16s ;" $nm_ $nm_] }
	if { $io_ == "out" } { return [format "\t\tsta_rif.%-16s = dyn_rif.%-16s ;" $nm_ $nm_] }
}
proc ReSim::rsv_print_port_slrm { ri_ nm_ io_ bw_ i args } {
	if { $io_ == "in" }  { return [format "\t`rsv_select_module_in ( %-16s )" $nm_] }
	if { $io_ == "out" } { return [format "\t`rsv_select_module_out( %-16s )" $nm_] }
}
proc ReSim::rsv_print_port_slei { ri_ nm_ io_ bw_ i args } {
	if { $io_ == "in" }  { return [format "\t`rsv_select_phase_in ( %-16s )" $nm_] }
	if { $io_ == "out" } { return [format "\t`rsv_select_phase_out( %-16s )" $nm_] }
}
proc ReSim::rsv_print_port_assg { ri_ nm_ io_ bw_ i args } {
	if { $io_ == "in" }  { return [format "\tassign sta_rif.%-16s = %-24s;" $nm_ $nm_] }
	if { $io_ == "out" } { return [format "\tassign %-24s = sta_rif.%-16s;" $nm_ $nm_] }
}
proc ReSim::rsv_print_port_svif { ri_ nm_ io_ bw_ i args } {
	if { $io_ == "in" } {set str "// rm: in  ---- static: out"}
	if { $io_ == "out"} {set str "// rm: out ---- static: in "}
	if { $bw_ == 1 } { return [format "\tlogic          %-16s; $str" $nm_] }
	if { $bw_ != 1 } { return [format "\tlogic  \[%2d:0\]  %-16s; $str" [expr $bw_ - 1] $nm_] }
}
proc ReSim::rsv_print_portmap { ri_ op_ {sep_ ""} args } {
	variable portmap_a

	# e.g.
	#    puts [ReSim::rsv_print_portmap $my_portmap_name io ,\n]
	#    puts [ReSim::rsv_print_portmap $my_portmap_name inst ,\n \ ]
	#    puts [ReSim::rsv_print_portmap $my_portmap_name inst ,\n rm0_rif.]
	#    puts [ReSim::rsv_print_portmap $my_portmap_name cnct \\\n]
	#    puts [ReSim::rsv_print_portmap $my_portmap_name slrm \n]
	#    puts [ReSim::rsv_print_portmap $my_portmap_name slei \n]
	#    puts [ReSim::rsv_print_portmap $my_portmap_name assg \n]
	#    puts [ReSim::rsv_print_portmap $my_portmap_name svif \n]

	set str ""; set i 0; set l_ [llength $portmap_a($ri_.pm)];
	foreach my_port $portmap_a($ri_.pm) {
		append str [eval rsv_print_port_$op_ $ri_ $my_port $i $args]
		incr i; if { $i != $l_ } { append str "$sep_" };
	}
	return $str
}
proc ReSim::rsv_print_x_injection { ri_ op_ } {
	variable portmap_a

	# e.g.
	#    puts [ReSim::rsv_print_x_injection $my_portmap_name dei]
	#    puts [ReSim::rsv_print_x_injection $my_portmap_name sei]
	
	set clk_ $portmap_a($ri_.clk); set str ""
	if { $clk_ != "" && $op_ == "dei" } {
		append str "\t// Toggle the clock of the reconfigurable module,\n"
		append str "\t// so that the X is propogated into the module.\n\n"
		append str "\tfork : ei_clocking_thread\n"
		append str "\t\tdei_vi.$clk_ = 1'b0;\n"
		append str "\t\trepeat(64) begin #2 dei_vi.clk = ~dei_vi.clk; end\n"
		append str "\tjoin_none\n\n"
	}
	
	if { $clk_ != "" && $op_ == "sei" } { 
		append str "\t// Drive undefined X values to all output signals\n"
		append str "\t// of the reconfigurable module.\n\n"
	}
	
	foreach my_port $portmap_a($ri_.pm) {
		set nm_ [lindex $my_port 0]; set io_ [lindex $my_port 1];
		if { $io_ == "in"  && $op_ == "dei" && $nm_ != $clk_ } {append str [format "\tdei_vi.%-16s <= 'hx;\n" $nm_]}
		if { $io_ == "out" && $op_ == "sei" && $nm_ != $clk_ } {append str [format "\tsei_vi.%-16s <= 'hx;\n" $nm_]}
	}
	
	return $str
}

proc ReSim::rsv_print_region_rif { rr_ nm_ gm_ sgnt_ i ri_ args} {
	return "\t$ri_    rm${i}_rif(); // reconfigurable module ${i}"
}
proc ReSim::rsv_print_region_sif { rr_ nm_ gm_ sgnt_ i ri_ args } {
	return "\tstate_rm_if          rm${i}_sif(); // reconfigurable module ${i}"
}
proc ReSim::rsv_print_region_pif { rr_ nm_ gm_ sgnt_ i ri_ args } {
	return "\t\t`rsv_init_portal(${i}, pif, \"$nm_\", $sgnt_)"
}
proc ReSim::rsv_print_region_cnctm { rr_ nm_ gm_ sgnt_ i ri_ args } {
	## TO BE REMOVED
	return "\t\t\t8'h${i}: begin `rsv_connect_module(rm_rif, rm${i}_rif) end"
}
proc ReSim::rsv_print_region_cncts { rr_ nm_ gm_ sgnt_ i ri_ args } {
	## TO BE REMOVED
	return "\t\t\t8'h${i}: begin `rsv_connect_state_spy(rm_sif, rm${i}_sif) end"
}
proc ReSim::rsv_print_region_slrmi { rr_ nm_ gm_ sgnt_ i ri_ args } {
	return "\t\t8'h${i}: begin rm${i}_rif.sig_ = rm_rif.sig_; end \\"
}
proc ReSim::rsv_print_region_slrmo { rr_ nm_ gm_ sgnt_ i ri_ args } {
	return "\t\t8'h${i}: begin rm_rif.sig_ = rm${i}_rif.sig_; end \\"
}
proc ReSim::rsv_print_region_ieia { rr_ nm_ gm_ sgnt_ i ri_ args } {
	## TO BE REMOVED
	return "\twire rm${i}_activated = (pif.active_module_id == 8'h${i});"
}
proc ReSim::rsv_print_region_ieib { rr_ nm_ gm_ sgnt_ i ri_ args } {
	## TO BE REMOVED
	return "\talways @(negedge rm${i}_activated) if(\$time!=0) `rsv_execute_tcl(interp, \$psprintf(\"ReSim::rsv_iei_hdl_state %m rm${i}\"))";
}
proc ReSim::rsv_print_region_module { rr_ nm_ gm_ sgnt_ i ri_ args } {
	return "\t$nm_ $gm_ rm${i} (\n[rsv_print_portmap $ri_ inst ,\n rm${i}_rif.]\n\t);"
}
proc ReSim::rsv_print_region_id { rr_ nm_ gm_ sgnt_ i ri_ args } {
	return [format "; %15s / %-15s ;       0x%02x / 0x%02x       ;" [lindex $args 0] $nm_ [lindex $args 1] $i]
}
proc ReSim::rsv_print_region_rstate { rr_ nm_ gm_ sgnt_ i ri_ args } {
	return "\t\t`rsv_execute_tcl(interp, \$psprintf(\"ReSim::rsv_register_state_spy %m rm${i} ./artifacts/spy/${rr_}_rm${i}.sll ./artifacts/sbt/${rr_}_rm${i}.sbt\"))"
}
proc ReSim::rsv_print_region_ustate { rr_ nm_ gm_ sgnt_ i ri_ args } {
	return "\t\t`rsv_execute_tcl(interp, \$psprintf(\"ReSim::rsv_unregister_state_spy %m rm${i}\"))"
}
proc ReSim::rsv_print_region_ignorebin { rr_ nm_ gm_ sgnt_ i ri_ args } {
	return "(${i}=>${i})"
}
proc ReSim::rsv_print_region { rr_ op_ {sep_ ""} args} {
	variable region_a

	# e.g.
	#    puts [ReSim::rsv_print_region $my_region_name rif \n]
	#    puts [ReSim::rsv_print_region $my_region_name sif \n]
	#    puts [ReSim::rsv_print_region $my_region_name pif \n]
	#    puts [ReSim::rsv_print_region $my_region_name cnctm \n]
	#    puts [ReSim::rsv_print_region $my_region_name cncts \n]
	#    puts [ReSim::rsv_print_region $my_region_name slrmi \n]
	#    puts [ReSim::rsv_print_region $my_region_name slrmo \n]
	#    puts [ReSim::rsv_print_region $my_region_name ieia \n]
	#    puts [ReSim::rsv_print_region $my_region_name ieib \n]
	#    puts [ReSim::rsv_print_region $my_region_name module \n]
	#    puts [ReSim::rsv_print_region $my_region_name id \n $rrid]
	#    puts [ReSim::rsv_print_region $my_region_name rstate \n $rrid]
	#    puts [ReSim::rsv_print_region $my_region_name ustate \n $rrid]
	#    puts [ReSim::rsv_print_region $my_region_name $rr_ ignorebin ,]

	set str ""; set i 0; set l_ [llength $region_a($rr_.rm)];
	foreach my_module $region_a($rr_.rm) {
		append str [eval rsv_print_region_$op_ $rr_ $my_module $i $region_a($rr_.ri) $args]
		incr i; if { $i != $l_ } { append str "$sep_" };
	}
	return $str
}

proc ReSim::rsv_print_fpga_rec { vf_ rec_ i args } {
	return "\t`include \"$rec_.svh\""
}
proc ReSim::rsv_print_fpga_ei { vf_ ei_ i args } {
	return "\t`include \"$ei_.svh\""
}
proc ReSim::rsv_print_fpga_scb { vf_ scb_ i args } {
	return "\t`include \"$scb_.svh\""
}
proc ReSim::rsv_print_fpga_ri { vf_ ri_ i args } {
	return "interface $ri_ ();\n[rsv_print_portmap $ri_ svif \n]\n\nendinterface: $ri_"
}
proc ReSim::rsv_print_fpga_rr_vcom { vf_ rr_ i args } {
	return "    vlog +incdir+./artifacts+\$RSV_HOME/src+\$OVM_HOME/src -L mtiReSim ./artifacts/$rr_.sv"
}
proc ReSim::rsv_print_fpga_rr_id { vf_ rr_ i args } {
	return [rsv_print_region $rr_ id "\n" $rr_ $i]
}
proc ReSim::rsv_print_fpga_rr_cvsig { vf_ rr_ i args } {
	return "\tint unsigned rr${i}_cur = 0; // RMid of the current active module in RR${i}"
}
proc ReSim::rsv_print_fpga_rr_cvspl { vf_ rr_ i args } {
	return "\t\tif(tr.rrid==${i}) rr${i}_cur = tr.rmid;"
}
proc ReSim::rsv_print_fpga_rr_cvp { vf_ rr_ i args } {
	variable region_a
	set lm1 [expr [llength $region_a($rr_.rm)]-1]; 
	
	set str "";
	append str "\t\tcvp_rr${i}_cur: coverpoint rr${i}_cur {\n";
	append str "\t\t\toption.weight=0;\n";
	append str "\t\t\tbins rr${i}_cur\[\] = {\[0:${lm1}\]};\n";
	append str "\t\t\tillegal_bins other = default;\n";
	append str "\t\t}\n";
	append str "\t\tcvp_rr${i}_cfg: coverpoint rr${i}_cur {\n";
	append str "\t\t\toption.weight=0;\n";
	append str "\t\t\tbins rr${i}_cfg\[\] = (\[0:${lm1}\] => \[0:${lm1}\]);\n";
	append str "\t\t\tignore_bins rr${i}_cfg_no_change = [rsv_print_region $rr_ ignorebin ,];\n";
	append str "\t\t\tillegal_bins other = default sequence;\n";
	append str "\t\t}";
	
	return $str;
}
proc ReSim::rsv_print_fpga_rr_cvcur { vf_ rr_ i args } {
	variable solyr_a
	
	if { [llength $solyr_a($vf_.rr)] == 1 } return ""
	return "cvp_rr${i}_cur"
}
proc ReSim::rsv_print_fpga_rr_cvcfg { vf_ rr_ i args } {
	variable solyr_a
	
	set str ""; set l_ [llength $solyr_a($vf_.rr)];
	for {set i_other 0} {$i_other<$l_} {incr i_other} {
		if { ${i} != ${i_other} } {
			append str "\t\tcross_rr${i}_cur_rr${i_other}_cfg: cross cvp_rr${i}_cur, cvp_rr${i_other}_cfg;\n"
		}
	}
	return $str;
}
proc ReSim::rsv_print_fpga { vf_ op_ {sep_ ""} args} {
	variable solyr_a

	# e.g.
	#    puts [ReSim::rsv_print_fpga $my_fpga_name rec \n]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name ei \n]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name scb \n]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name ri \n\n]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name rr \n _vcom]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name rr \n _id]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name rr \n _cvsig]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name rr \n _cvspl]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name rr \n _cvp]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name rr , _cvcur]
	#    puts [ReSim::rsv_print_fpga $my_fpga_name rr \n _cvcfg]

	set str ""; set i 0; set l_ [llength $solyr_a($vf_.$op_)];
	foreach my_ $solyr_a($vf_.$op_) {
		append str [eval rsv_print_fpga_$op_[lindex $args 0] $vf_ $my_ $i [lrange $args 1 end]]
		incr i; if { $i != $l_ } { append str "$sep_" };
	}
	return $str
}

proc ReSim::rsv_print_cp_io { vf_ cp_ i args } {
	set str    "\toutput     BUSY,\n\toutput     \[31:0\] O,\n"
	append str "\tinput      CLK, \n\tinput      \[31:0\] I,\n"
	
	if { $cp_ == "ICAP_VIRTEX4_WRAPPER" } { append str "\tinput      CE, \n\tinput      WRITE" }
	if { $cp_ == "ICAP_VIRTEX5_WRAPPER" } { append str "\tinput      CE, \n\tinput      WRITE" }
	if { $cp_ == "ICAP_VIRTEX6_WRAPPER" } { append str "\tinput      CSB,\n\tinput      RDWRB" }
	
	return str;
}
proc ReSim::rsv_print_cp_assg { vf_ cp_ i args } {
	return "";
}
proc ReSim::rsv_print_cp { vf_ op_ } {
	variable solyr_a

	# e.g.
	#    puts [ReSim::rsv_print_cp $my_fpga_name io]
	#    puts [ReSim::rsv_print_cp $my_fpga_name assg]
	
	set cp_ $solyr_a($vf_.cp)
	return [rsv_print_cp_$op_ $vf_ $cp_ 0]
}

proc ReSim::rsv_update_rec_ei_ri { vf_ op_ } {
	variable region_a
	variable solyr_a

	# e.g.
	#    puts [ReSim::rsv_update_rec_ei_ri $my_fpga_name rec]
	#    puts [ReSim::rsv_update_rec_ei_ri $my_fpga_name ei]
	#    puts [ReSim::rsv_update_rec_ei_ri $my_fpga_name ri]

	foreach my_region $solyr_a($vf_.rr) {
		set my_ $region_a($my_region.$op_)
		if { $my_ != "" && [lsearch $solyr_a($vf_.$op_) $my_] < 0 } { lappend solyr_a($vf_.$op_) $my_ };
	}
}

#############################################
## Code generation
#############################################

namespace eval ReSim {
	namespace export rsv_gen_solyr

	variable portmap_a
	variable region_a
	variable solyr_a
}

proc ReSim::rsv_gen_region { rr_ id_ } {
	global RSV_HOME
	variable region_a

	set nm_  $region_a($rr_.nm)
	set ri_  $region_a($rr_.ri)
	set sz_  $region_a($rr_.sz)
	set rec_ $region_a($rr_.rec)
	set ei_  $region_a($rr_.ei)
	set rm_  $region_a($rr_.rm)
	set l_   [llength $region_a($rr_.rm)]

	# Class-based part of the Reconfigurable Region: region_recorder
	if { $rec_ != ""} {
		set f [open "./artifacts/$rec_.svh" w+]; fconfigure $f -translation lf;
		source $RSV_HOME/scripts/rsvgen_region_recorder.tcl; puts $f $str;
		close $f
	} else {
		set rec_ "rsv_region_recorder#(${ri_}_type)"
	}

	# Class-based part of the Reconfigurable Region: error injector
	if { $ei_ != ""} {
		set f [open "./artifacts/$ei_.svh" w+]; fconfigure $f -translation lf;
		source $RSV_HOME/scripts/rsvgen_error_injector.tcl; puts $f $str;
		close $f
	} else {
		set ei_ "rsv_error_injector#(${ri_}_type)"
	}
	
	# Module-based part of the Reconfigurable Region: module wrappers, sbt, sll file
	set i 0; foreach my_module $region_a($rr_.rm) {
		set f [open "./artifacts/synth/${rr_}_rm${i}.v" w+]; fconfigure $f -translation lf;
		source $RSV_HOME/scripts/rsvgen_module.tcl; puts $f $str;
		close $f
		
		set f [open "./artifacts/synth/${rr_}_rm${i}_bb.v" w+]; fconfigure $f -translation lf;
		source $RSV_HOME/scripts/rsvgen_module_bb.tcl; puts $f $str;
		close $f
		
		# frame address & word count
		set fa [expr (($id_ << 24) | ($i << 16) | 0 )]
		set wc [expr $sz_ * 4]
		
		# generate the binary sbt file
		set sgnt [rsv_gen_sbt "./artifacts/sbt/${rr_}_rm${i}" WCFG $fa $wc]
		lset region_a($rr_.rm) $i 2 [format "32'h%08x" $sgnt]
		
		# parse sbt (convert binary sbt file into 2 txt format files
		# one for the entire sbt, and one for the configuration data part)
		rsv_parse_sbt "./artifacts/sbt/${rr_}_rm${i}"
		
		# generate the sll file
		set f [open "./artifacts/spy/${rr_}_rm${i}.sll" w+]; fconfigure $f -translation lf;
		puts $f "// ==== Logic Allocation File (ReSim) ====";
		puts $f "// ==== Format: \$frame_address \$offset \$bitwidth \$signal_path";
		close $f
		
		incr i;
	}

	# Module-based part of the Reconfigurable Region: Extended Portal
	set f [open "./artifacts/$rr_.sv" w+]; fconfigure $f -translation lf;
	source $RSV_HOME/scripts/rsvgen_region.tcl; puts $f $str;
	close $f
}
proc ReSim::rsv_gen_solyr { vf_ } {
	global RSV_HOME
	variable solyr_a

	set nm_ $solyr_a($vf_.nm)
	set cp_ $solyr_a($vf_.cp)
	set scb_ $solyr_a($vf_.scb)
	set rr_ $solyr_a($vf_.rr)
	set l_  [llength $solyr_a($vf_.rr)]

	rsv_update_rec_ei_ri $vf_ rec; set rec_ solyr_a($vf_.rec) 
	rsv_update_rec_ei_ri $vf_ ei;  set ei_  solyr_a($vf_.ei)  
	rsv_update_rec_ei_ri $vf_ ri;  set ri_  solyr_a($vf_.ri)  

	# All reconfigurable regions, region_recorders, error injectors of the simulation-only layer
	set i 0; foreach my_region $solyr_a($vf_.rr)  {
		rsv_gen_region $my_region $i; incr i; 
	}

	# The configuration port (class & module) of the simulation-only layer
	set f [open "./artifacts/icap_virtex_wrapper.sv" w+]; fconfigure $f -translation lf;
	source $RSV_HOME/scripts/rsvgen_configuration_port.tcl; puts $f $str;
	close $f
	file copy -force $RSV_HOME/scripts/wrp/icap_virtex_wrapper.txt ./artifacts/synth/icap_virtex_wrapper.vhd

	# The scoreboard of the simulation-only layer
	if { $scb_ != ""} {
		set f [open "./artifacts/$scb_.svh" w+]; fconfigure $f -translation lf;
		source $RSV_HOME/scripts/rsvgen_scoreboard.tcl; puts $f $str;
		close $f
	} else {
		set scb_ "rsv_scoreboard"
	}
	
	# The top-level simulation-only layer
	set f [open "./artifacts/$vf_.sv" w+]; fconfigure $f -translation lf;
	source $RSV_HOME/scripts/rsvgen_solyr.tcl; puts $f $str;
	close $f

	# The usr package
	set f [open "./artifacts/usr_solyr_pkg.svp" w+]; fconfigure $f -translation lf;
	source $RSV_HOME/scripts/rsvgen_usr_pkg.tcl; puts $f $str;
	close $f

	# The usr interfaces
	set f [open "./artifacts/usr_ifs.sv" w+]; fconfigure $f -translation lf;
	source $RSV_HOME/scripts/rsvgen_usr_ifs.tcl; puts $f $str;
	close $f

	# The report
	set f [open "./artifacts/${vf_}_report.txt" w+]; fconfigure $f -translation lf;
	source $RSV_HOME/scripts/rsvgen_report.tcl; puts $f $str;
	close $f

	# The TODO LIST file
	set f [open "./artifacts/${vf_}_todolist.txt" w+]; fconfigure $f -translation lf;
	source $RSV_HOME/scripts/rsvgen_todolist.tcl; puts $f $str;
	close $f
}

