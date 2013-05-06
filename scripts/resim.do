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

file mkdir ./artifacts/
file mkdir ./artifacts/sbt
file mkdir ./artifacts/spy
file mkdir ./artifacts/synth

namespace eval ReSim {
	namespace export rsv_assert
	namespace export rsv_assertt
}

proc ReSim::rsv_warning {cond {msg "ReSim::rsv_warning $cond"}} {
	# e.g. rsv_warning { $my_var <= 100 }, procedure warning
	if {![uplevel 1 expr $cond]} {puts $msg}
}
proc ReSim::rsv_assert {cond {msg "ReSim::rsv_assert $cond"}} {
	# e.g. rsv_assert { $my_var <= 100 }, procedure assertion
	if {![uplevel 1 expr $cond]} {return -code error $msg}
}
proc ReSim::rsv_assertt {my_var cond} {
	# e.g. assertt my_list { [llength $my_list]<10 }, concurrent assertion
	uplevel 1 [list trace var $my_var w "ReSim::rsv_assertt $cond ;#"]
}

source $RSV_HOME/scripts/rsv_code_generation.do
source $RSV_HOME/scripts/rsv_sbt_manager.do
source $RSV_HOME/scripts/rsv_state_spy.do
