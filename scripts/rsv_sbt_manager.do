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
	namespace export rsv_create_memory
	namespace export rsv_add_2_memory
	
	namespace export rsv_gen_sbt
	namespace export rsv_parse_sbt
	
	variable mem_a
}

proc ReSim::rsv_gen_sbt { sbt_ cfg_ fa_ wc_ {bit_ ""} } {
	
	rsv_assert { [string is integer $fa_] == 1 } \
		"\[ERROR\] Frame address ($fa_) should be an integer!!!"
	rsv_assert { [string is integer $wc_] == 1 } \
		"\[ERROR\] Word count ($wc_) should be an integer!!!"
	rsv_assert { [string equal $cfg_ "WCFG"] == 1 || [string equal $cfg_ "RCFG"] == 1 || \
		[string equal $cfg_ "MSK0"] == 1 || [string equal $cfg_ "MSK1"] == 1 } \
		"\[ERROR\] Operation can only be WCFG, RCFG, MSK0, MSK1!!!"
	
	# prepare for sbt fields
	if { $cfg_ == "WCFG" || $cfg_ == "MSK0" || $cfg_ == "MSK1"} {
		set sbt_cfg "00000001"
		set sbt_fdr "30004000"
	}
	if { $cfg_ == "RCFG" } {
		set sbt_cfg "00000004"
		set sbt_fdr "28006000"
	}
	set sbt_size [format "50%06X" $wc_]
	set sbt_far [format "%08X" $fa_]

	# sbt mid & signature
	set sbt_buffer_mid {}
	set my_sgnt 0
	for {set i 0} {$i < $wc_} {incr i} {
	
		set cdata 0
		if { $cfg_ == "WCFG" && [expr $i % 4] == 0 } {
			set cdata [expr (int(0x10000 * rand()) << 16) + int(0x10000 * rand())]
			set my_sgnt [expr $my_sgnt ^ $cdata]
			
		} elseif { $cfg_ == "MSK1" } {
			set cdata 0x00007000
			
		}
		lappend sbt_buffer_mid [format "%08X" $cdata]
	}
	set sbt_sgnt [format "%08X" $my_sgnt]

	# sbt header & ending
	set sbt_buffer_header [list \
		"AA995566" "20000000" "30000001" "$sbt_sgnt" \
		"30002001" "$sbt_far" "30008001" "$sbt_cfg"  \
		"$sbt_fdr" "$sbt_size" \
	]

	set sbt_buffer_end [list  \
		"20000000" "20000000" "30008001" "0000000D" \
		"20000000" "20000000" \
	];
	
	# generating sbt file (BIG ENDIAN)
	set f [open "${sbt_}.sbt" w+]; fconfigure $f -translation binary;
	
	foreach my_line [concat $sbt_buffer_header $sbt_buffer_mid $sbt_buffer_end] {
		puts -nonewline $f [binary format H8 $my_line]
	}
	close $f
	
	return $my_sgnt
}

proc ReSim::rsv_parse_sbt_get_word { f_ w_ } {
	upvar $w_ my_word
	binary scan [read $f_ 4] H8 my_word
	set my_word "0x$my_word"
	
	if {[eof $f_]} { return 0 } else {return 1}
}
proc ReSim::rsv_parse_sbt_type { my_word } {
	if { [expr ($my_word & 0xe0000000) == 0x20000000 ] } { return "Type 1"} 
	if { [expr ($my_word & 0xe0000000) == 0x40000000 ] } { return "Type 2"} 
	else { return "Unknown Header Type" }
}
proc ReSim::rsv_parse_sbt_op { my_word } {
	if { [expr ($my_word & 0x18000000) == 0x08000000 ] } { return "Rd" }
	if { [expr ($my_word & 0x18000000) == 0x10000000 ] } { return "Wr" } 
	else { return "Unknown Header Op" }
}
proc ReSim::rsv_parse_sbt_cregs { my_word } {
	if { [expr ($my_word & 0x0003e000) == 0x00000000 ] } { return "CRC" 
	} elseif { [expr ($my_word & 0x0003e000) == 0x00008000 ] } { return "CMD" 
	} elseif { [expr ($my_word & 0x0003e000) == 0x0000e000 ] } { return "STAT"
	} elseif { [expr ($my_word & 0x0003e000) == 0x00002000 ] } { return "FAR" 
	} elseif { [expr ($my_word & 0x0003e000) == 0x00004000 ] } { return "FDRI"
	} elseif { [expr ($my_word & 0x0003e000) == 0x00006000 ] } { return "FDRO"
	} elseif { [expr ($my_word & 0x0003e000) == 0x00018000 ] } { return "ID"  
	} elseif { [expr ($my_word & 0x0003e000) == 0x0000a000 ] } { return "CTL" 
	} elseif { [expr ($my_word & 0x0003e000) == 0x0000c000 ] } { return "MASK"
	} elseif { [expr ($my_word & 0x0003e000) == 0x00012000 ] } { return "COR1"
	} else { return "Unknown Header Register" }
}
proc ReSim::rsv_parse_sbt_t1h_wc { my_t1h } {
	return [expr $my_t1h & 0x000003ff]
}
proc ReSim::rsv_parse_sbt_t2h_wc { my_t2h } {
	return [expr $my_t2h & 0x03ffffff]
}
proc ReSim::rsv_parse_sbt_t1h_string { addr my_t1h } {
	return "[format @%x $addr] [format %08X $my_t1h] // [rsv_parse_sbt_type $my_t1h] [rsv_parse_sbt_op $my_t1h] [rsv_parse_sbt_cregs $my_t1h]"
}
proc ReSim::rsv_parse_sbt_t2h_string { addr my_t2h } {
	return "[format @%x $addr] [format %08X $my_t2h] // [rsv_parse_sbt_type $my_t2h] [rsv_parse_sbt_op $my_t2h] [rsv_parse_sbt_t2h_wc $my_t2h] Words"
}
proc ReSim::rsv_parse_sbt_data_string { addr my_data my_t1h } {
	
	if { [expr ($my_t1h & 0x0003e000) == 0x00008000 ] } {
		if { [expr ($my_data & 0x1f) == 0x00 ] } { set my_c "Null" 
		} elseif { [expr ($my_data & 0x1f) == 0x01 ] } { set my_c "WCFG" 
		} elseif { [expr ($my_data & 0x1f) == 0x04 ] } { set my_c "RCFG" 
		} elseif { [expr ($my_data & 0x1f) == 0x03 ] } { set my_c "LFRM" 
		} elseif { [expr ($my_data & 0x1f) == 0x05 ] } { set my_c "START" 
		} elseif { [expr ($my_data & 0x1f) == 0x08 ] } { set my_c "AHIGH" 
		} elseif { [expr ($my_data & 0x1f) == 0x07 ] } { set my_c "RCRC" 
		} elseif { [expr ($my_data & 0x1f) == 0x0a ] } { set my_c "GRESTORE" 
		} elseif { [expr ($my_data & 0x1f) == 0x0c ] } { set my_c "GCAPTURE" 
		} elseif { [expr ($my_data & 0x1f) == 0x0d ] } { set my_c "DESYNC" 
		} else { set my_c "Unknown Command" }
		
	} elseif { [expr ($my_t1h & 0x0003e000) == 0x00002000 ] } {
		
		set rrid [format "0x%02x" [expr ( ($my_data >> 24) & 0x00ff) ] ]
		set rmid [format "0x%02x" [expr ( ($my_data >> 16) & 0x00ff) ] ]
		set mna  [format "0x%04x" [expr ( ($my_data >> 0)  & 0xffff) ] ]
		
		set my_c "RRid:$rrid, RMid:$rmid, MNA:$mna"
		
	} elseif { [expr ($my_t1h & 0x0003e000) == 0x00000000 ] } { set my_c "Signature" 
	} elseif { [expr ($my_t1h & 0x0003e000) == 0x00018000 ] } { set my_c "IDCODE" 
	} else { set my_c [format "%08X" $my_data] }
	
	return "[format @%x $addr] [format %08X $my_data] // $my_c"
}
proc ReSim::rsv_parse_sbt_cdata_string { addr my_data i } {
	return "[format @%x $addr] [format %08X $my_data] // SBT Word $i"
}
proc ReSim::rsv_parse_sbt_cdata_string_2 { caddr my_data } {
	return "[format @%x $caddr] [format %08X $my_data]"
}
proc ReSim::rsv_parse_sbt { sbt_ } {
	
	rsv_assert { [file exists "${sbt_}.sbt"] == 1 } \
		"\[ERROR\] Simulation-only bitstream (sbt) file ${sbt_}.sbt does not exist!!!"
	
	set f_sbt [open "${sbt_}.sbt" r+]; fconfigure $f_sbt -translation binary;
	set f_txt [open "${sbt_}.txt" w+]; fconfigure $f_txt -translation lf;
	set f_cd [open "${sbt_}_cdata.txt" w+]; fconfigure $f_cd -translation lf;
	
	puts $f_txt "// ==== Name: ${sbt_}.txt (Simulation-only Bitstream)"
	puts $f_txt "// ==== Time: [clock format [clock seconds] -format  {%H:%M:%S, %B %d, %Y}] "
	
	puts $f_cd "// ==== Name: ${sbt_}_cdata.txt (Simulation-only Bitstream, Configuration Data Section)"
	puts $f_cd "// ==== Time: [clock format [clock seconds] -format  {%H:%M:%S, %B %d, %Y}] "
	
	set addr 0; set caddr 0;
	while {1} {
		if { [rsv_parse_sbt_get_word $f_sbt my_t1h] == 0 } { break }
		
		# parse sync/dummy/nop packet
		if { $my_t1h == 0xaa995566 } { puts $f_txt "[format @%x $addr] AA995566 // SYNC"; incr addr; continue;}
		if { $my_t1h == 0xffffffff } { puts $f_txt "[format @%x $addr] FFFFFFFF // Dummy"; incr addr; continue;}
		if { $my_t1h == 0x20000000 } { puts $f_txt "[format @%x $addr] 20000000 // Type 1 Nop"; incr addr; continue;}
		
		# parse t1/t2 header section
		if { [rsv_parse_sbt_t1h_wc $my_t1h] != 0 } {
			set my_wc [rsv_parse_sbt_t1h_wc $my_t1h]
			puts $f_txt [rsv_parse_sbt_t1h_string $addr $my_t1h]; incr addr;
		
		} else {
			rsv_parse_sbt_get_word $f_sbt my_t2h
			set my_wc [rsv_parse_sbt_t2h_wc $my_t2h]
			
			puts $f_txt [rsv_parse_sbt_t1h_string $addr $my_t1h]; incr addr;
			puts $f_txt [rsv_parse_sbt_t2h_string $addr $my_t2h]; incr addr;
		}
		
		# parse data section
		if { $my_wc == 1 } {
			rsv_parse_sbt_get_word $f_sbt my_data
			puts $f_txt [rsv_parse_sbt_data_string $addr $my_data $my_t1h]; incr addr
		} else {
			for {set i 0} {$i < $my_wc} {incr i} {
				rsv_parse_sbt_get_word $f_sbt my_data
				puts $f_txt [rsv_parse_sbt_cdata_string $addr $my_data $i]; incr addr
				puts $f_cd [rsv_parse_sbt_cdata_string_2 $caddr $my_data]; incr caddr
			}
		}
	}
	
	close $f_sbt
	close $f_txt
	close $f_cd
	
}

proc ReSim::rsv_create_memory { mem_ gra_ nbk_ edi_ } {
	global RSV_HOME
	variable mem_a
	
	rsv_assert { [llength [array names mem_a -exact $mem_.nm]] == 0 } \
		"\[ERROR\] memory $mem_ has already been created!!!"
	rsv_assert { $gra_ == 1 || $gra_ == 2 || $gra_ == 4 || $gra_ == 8 } \
		"\[ERROR\] only support memory granularity (smallest addressable unit) of 1/2/4/8 bytes!!!"
	rsv_assert { $nbk_ == 1 || $nbk_ == 2 || $nbk_ == 4 || $nbk_ == 8 } \
		"\[ERROR\] only support memory that has 1/2/4/8 banks!!!"
	rsv_assert { [expr ($gra_ *  $nbk_)%4] == 0} \
		"\[ERROR\] memory granularity * memory bank should be multiple of 4 since bitstream is 32bit aligned !!!"
	rsv_assert { [string equal [string tolower $edi_] le] == 1 || [string equal [string tolower $edi_] be] == 1} \
		"\[ERROR\] memory endian should be either little endian (le) OR big endian (be)!!!"
	
	set mem_a($mem_.nm) $mem_
	set mem_a($mem_.gra) $gra_
	set mem_a($mem_.nbk) $nbk_
	set mem_a($mem_.edi) [string tolower $edi_]
	set mem_a($mem_.sbt) {}
	
	for {set i 0} {$i < $mem_a($mem_.nbk)} {incr i} {
		set f [open "./artifacts/sbt/${mem_}_bank$i.txt" w+];
		
		puts $f "// ==== Name: ${mem_}_bank$i.txt "
		puts $f "// ==== Time: [clock format [clock seconds] -format  {%H:%M:%S, %B %d, %Y}] "
		
		close $f
	}
}
proc ReSim::rsv_add_2_memory { mem_ bit_ addr_ } {
	global RSV_HOME
	variable mem_a

	rsv_assert { [llength [array names mem_a -exact $mem_.nm]] == 1 } \
		"\[ERROR\] memory $mem_ should be created before adding modules!!!"
	rsv_assert { [file exists ${bit_}] == 1 } \
		"\[ERROR\] simulation-only bitstream should be created before adding to memory!!!"
		
	set my_sbt [list $bit_ $addr_]
	lappend mem_a($mem_.sbt) $my_sbt
	
	set gra_ $mem_a($mem_.gra)
	set nbk_ $mem_a($mem_.nbk)
	set edi_ $mem_a($mem_.edi)
	
	set fmem_l {}
	for {set i 0} {$i < $mem_a($mem_.nbk)} {incr i} {
		set fmem_ "./artifacts/sbt/${mem_}_bank$i.txt"
		lappend fmem_l $fmem_
	}
	
	eval "exec python $RSV_HOME/scripts/rsvsbt_memory.py $gra_ $edi_ $bit_ $addr_ $fmem_l"
	
}
