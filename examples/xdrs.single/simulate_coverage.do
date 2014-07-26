
.main clear; quit -sim; do settings.do;

# create libraries
if { [file exists work] } { vdel -lib work -all }; vlib work;
if { [file exists mtiReSim] } { vdel -lib mtiReSim -all }; vlib mtiReSim;

if { [file exists xtests] } { foreach item [glob -nocomplain -dir xtests *.txt] {file delete -force $item} }
if { [file exists xtests] } { foreach item [glob -nocomplain -dir xtests *.wlf] {file delete -force $item} }

if { [file exists coverage/merged.ucdb] } { foreach item [glob -nocomplain -dir coverage *] {file delete -force $item} }
file delete -force ./coverage/htmlrpt

# import testplan
xml2ucdb -format Excel testplan.xml coverage/testplan.ucdb

# compile xdrs
vlog +acc +cover=sbfec -coverexcludedefault -sv "./xdrs/cores/reverse.v"
vlog +acc +cover=sbfec -coverexcludedefault -sv "./xdrs/cores/maximum.v"
vlog +acc +cover=sbfec -coverexcludedefault -sv "./xdrs/cores/intern_sync.v"
vlog +acc +cover=sbfec -coverexcludedefault -sv "./xdrs/cores/filter_sync.v"
vlog +acc +cover=sbfec -coverexcludedefault -sv "./xdrs/cores/stat_cnt.v"
vlog +acc +cover=sbfec -coverexcludedefault -sv "./xdrs/isolator.v"
vlog +acc +cover=sbfec -coverexcludedefault -sv "./xdrs/icapi.v"

vlog +acc +incdir+$OVM_HOME/src "./xdrs/prodcons.sv"
vlog +acc +incdir+$OVM_HOME/src "./xdrs/manager.sv"
vlog +acc +incdir+$OVM_HOME/src "./xdrs/memctrl.sv"
vlog +acc "./xdrs/xbuscore.v"

# compile ReSim
vlog -work mtiReSim +acc "$RSV_HOME/src/rsv_ifs.sv"
vlog -work mtiReSim +acc +incdir+$RSV_HOME/src+$OVM_HOME/src "$RSV_HOME/src/rsv_solyr_pkg.svp"
vlog -work mtiReSim +acc "./artifacts/usr_ifs.sv"
vlog -work mtiReSim +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src "./artifacts/usr_solyr_pkg.svp"

# compile artifacts
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim +define+MTI_QUESTA "./artifacts/icap_virtex_wrapper.sv"
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim +define+MTI_QUESTA "./artifacts/my_region.sv"
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim +define+MTI_QUESTA "./artifacts/my_solyr.sv"

# run all tests and collect coverage data.txt

set alldirecteditems [list \
	"TEST_DPR_DEMO" "TEST_DPR_SIMPLE" "TEST_DPR_READBACK" "TEST_DPR_ISOLATION" "TEST_DPR_RETRY" \
]
set allrandomitems [list \
	[list "TEST_DPR_RANDOM" 76] \
	[list "TEST_DPR_RANDOM" 92] \
	[list "TEST_DPR_RANDOM" [expr int(rand() * 100)]] \
	[list "TEST_DPR_RANDOM" [expr int(rand() * 100)]] \
]

foreach oneitem [concat $alldirecteditems $allrandomitems] {
	
	if { [llength $oneitem] == 1 } {
		set oneseed 0
		set onetest $oneitem
		set onetestfile [string replace [string tolower $onetest] 0 7 "tdpr"]
		set onetestname $onetest
	} else {
		set oneseed [lindex $oneitem 1]
		set onetest [lindex $oneitem 0]
		set onetestfile [string replace [string tolower $onetest] 0 7 "tdpr"]_[format "%02d" ${oneseed}]
		set onetestname ${onetest}_[format "%02d" ${oneseed}]
	}
	transcript file ./xtests/$onetestfile.txt
	
	# compile onetest & load simulation
	vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src+./xtests -L mtiReSim +define+$onetest "./xdrs/xdrs.sv"
	vsim -t ps -coverage -assertdebug -sv_seed $oneseed -permit_unmatched_virtual_intf -L mtiReSim \
		-wlf ./xtests/$onetestfile.wlf -l ./xtests/$onetestfile.txt xdrs
	
	mem load -filltype value -fillradix hex -filldata 0 /xdrs/mem_0/zbtmem;
	mem load -infile ./artifacts/sbt/zbt_bank0.txt -format hex /xdrs/mem_0/zbtmem
	mem load -infile ./artifacts/sbt/zbt_bank0.rb.txt -format hex /xdrs/mem_0/zbtmem

	do coverageexclusions.do
	
	# start simulation & state spy
	echo "*******************************************"
	echo "*******************************************"
	echo "                 $onetestname"
	echo "*******************************************"
	echo "*******************************************"
	
	onfinish stop; onbreak {resume}
	
	run -all
	
	coverage attribute -name TESTNAME -value $onetestname
	coverage attribute -name "Simulator" -value [vsimVersionString]
	coverage save coverage/$onetestfile.ucdb
}

# merge the coverage data and generate report
transcript file ./coverage.txt
vcover merge -strip 0 ./coverage/merged.ucdb ./coverage/*.ucdb
vcover report -html -htmldir ./coverage/covhtmlrpt ./coverage/merged.ucdb
vcover ranktest -verbose -plansection / -rankfile ./coverage/merged.rank coverage/*.ucdb

transcript file transcript
file delete -force vcover.log

vsim -viewcov ./coverage/merged.ucdb
add testbrowser ./coverage/merged.ucdb
add testbrowser ./coverage/merged.rank

