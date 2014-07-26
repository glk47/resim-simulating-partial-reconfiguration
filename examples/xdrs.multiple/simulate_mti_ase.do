
.main clear; quit -sim; do settings.do;

# create libraries
if { [file exists work] } { vdel -lib work -all }; vlib work;
if { [file exists mtiReSim] } { vdel -lib mtiReSim -all }; vlib mtiReSim;

# compile OVM
# Note: This step is only required if your simulator does not have a built-in OVM library
# In particular, ModelSim-ASE does not have a built-in OVM library while QuestaSim has
vlog -work mtiReSim +incdir+$OVM_HOME/src "$OVM_HOME/src/ovm_pkg.sv"

# compile xdrs
vlog +acc "./xdrs/lpfilter/gfirMAC.v"
vlog +acc "./xdrs/lpfilter/gfirTF.v"
vlog +acc -sv "./xdrs/lpfilter/pipeline_sync.v"
vlog +acc -sv "./xdrs/lpfilter/lpfilter.v"
vlog +acc "./xdrs/cores/reverse.v"
vlog +acc "./xdrs/cores/maximum.v"
vlog +acc "./xdrs/cores/intern_sync.v"
vlog +acc "./xdrs/cores/filter_sync.v"
vlog +acc "./xdrs/cores/stat_cnt.v"
vlog +acc -sv "./xdrs/region_wrapper.v"
vlog +acc "./xdrs/isolator.v"
vlog +acc -sv "./xdrs/icapi.v"

vlog +acc +incdir+$OVM_HOME/src -L mtiReSim "./xdrs/prodcons.sv"
vlog +acc +incdir+$OVM_HOME/src -L mtiReSim "./xdrs/manager.sv"
vlog +acc +incdir+$OVM_HOME/src -L mtiReSim "./xdrs/memctrl.sv"
vlog +acc "./xdrs/xbuscore.v"

# compile ReSim
vlog -work mtiReSim +acc "$RSV_HOME/src/rsv_ifs.sv"
vlog -work mtiReSim +acc +incdir+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "$RSV_HOME/src/rsv_solyr_pkg.svp"
vlog -work mtiReSim +acc "./artifacts/usr_ifs.sv"
vlog -work mtiReSim +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/usr_solyr_pkg.svp"

# compile artifacts
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/math_0_rr.sv"
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/math_1_rr.sv"
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/lpfilter_2_rr.sv"
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/icap_virtex_wrapper.sv"
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/my_solyr.sv"

# TEST_DPR_STREAMING TEST_DPR_RANDOM
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src+./xtests -L mtiReSim +define+TEST_DPR_STREAMING "./xdrs/xdrs.sv"

# load simulation
vsim -t ps -permit_unmatched_virtual_intf -L mtiReSim xdrs

mem load -filltype value -fillradix hex -filldata 0 /xdrs/mem_0/zbtmem;
mem load -infile ./artifacts/sbt/zbt_bank0.txt -format hex /xdrs/mem_0/zbtmem
mem load -infile ./artifacts/sbt/zbt_bank0.rb.txt -format hex /xdrs/mem_0/zbtmem

do debug.do

# start simulation
run 10ns
add wave -noupdate -expand -group icap -expand //solyr/rr0/rec/sbt_trans
add wave -noupdate -expand -group icap -expand //solyr/rr1/rec/sbt_trans
add wave -noupdate -expand -group icap -expand //solyr/rr2/rec/sbt_trans

run -all

