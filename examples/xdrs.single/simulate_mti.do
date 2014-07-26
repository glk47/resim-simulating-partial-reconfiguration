
.main clear; quit -sim; do settings.do;

# create libraries
if { [file exists work] } { vdel -lib work -all }; vlib work;
if { [file exists mtiReSim] } { vdel -lib mtiReSim -all }; vlib mtiReSim;

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

# TEST_DPR_DEMO TEST_DPR_SIMPLE TEST_DPR_READBACK TEST_DPR_ISOLATION TEST_DPR_RETRY TEST_DPR_RANDOM
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src+./xtests -L mtiReSim +define+TEST_DPR_DEMO "./xdrs/xdrs.sv"

# load simulation
vsim -t ps -assertdebug -sv_seed 0 -permit_unmatched_virtual_intf -L mtiReSim xdrs

mem load -filltype value -fillradix hex -filldata 0 /xdrs/mem_0/zbtmem;
mem load -infile ./artifacts/sbt/zbt_bank0.txt -format hex /xdrs/mem_0/zbtmem
mem load -infile ./artifacts/sbt/zbt_bank0.rb.txt -format hex /xdrs/mem_0/zbtmem

do debug.do

# start simulation
onfinish stop; onbreak {resume}

profile on -p
profile on -m

run 10ns
add wave -noupdate -expand -group icap -expand //solyr/rr0/rec/sbt_trans

run -all

profile report -structural
profile report -du
