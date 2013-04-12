
.main clear; quit -sim; do settings.do; 

# compile design & testbench
#===========================

if { [file exists work] } { vdel -lib work -all }; vlib work;
if { [file exists mtiReSim] } { vdel -lib mtiReSim -all }; vlib mtiReSim;

vlog -f board_rtl.f
vlog -f board_tb.f

# compile sim-only artifacts
#===========================

vlog -work mtiReSim $RSV_HOME/src/rsv_ifs.sv
vlog -work mtiReSim +incdir+$RSV_HOME/src+$OVM_HOME/src $RSV_HOME/src/rsv_solyr_pkg.svp
vlog -work mtiReSim ./artifacts/usr_ifs.sv
vlog -work mtiReSim +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src ./artifacts/usr_solyr_pkg.svp

vlog +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim ./artifacts/pcie_app_v6.sv
vlog +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim ./artifacts/icap_virtex_wrapper.sv
vlog +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim ./artifacts/pcie_solayer.sv

# load design and tests
#======================

vsim -novopt +notimingchecks +nowarnTFMPC +nowarnPCDPC -permit_unmatched_virtual_intf \
	+PCIE_TESTNAME=Demo_Test_Using_ReSim +define+SIMULATION \
	-L work -L mtiReSim -L secureip -L unisims_ver -L XilinxCoreLib_ver work.board work.glbl

do wave_mti.do
mem load -infile ./artifacts/sbt/mem_bank0.txt -format hex /board/RP/tx_usrapp/sbtmem

# start simulation
#=============================

run 10ns
add wave -noupdate -expand -group loader -expand //solyr/rr0/rec/sbt_trans

run 80us
