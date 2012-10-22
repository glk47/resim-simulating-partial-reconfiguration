
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
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/icap_virtex_wrapper.sv"
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/my_region.sv"
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/my_solyr.sv"

# TEST_DPR_DEMO
vlog +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src+./xtests -L mtiReSim +define+TEST_DPR_R "./xdrs/xdrs.sv"

# load simulation
vsim -t ps -assertdebug -sv_seed 0 -permit_unmatched_virtual_intf -L mtiReSim xdrs

mem load -filltype value -fillradix hex -filldata 0 /xdrs/mem_0/zbtmem;
mem load -infile ./artifacts/sbt/zbt_bank0.txt -format hex /xdrs/mem_0/zbtmem
mem load -infile ./artifacts/sbt/zbt_bank0.rb.txt -format hex /xdrs/mem_0/zbtmem

# add wave
add wave -noupdate -format Logic -radix hex /xdrs/clk

add wave -noupdate -expand -group mgr -label req_n  -radix hex /xdrs/mgr_0/rc0_reqn
add wave -noupdate -expand -group mgr -label ack_n  -radix hex /xdrs/mgr_0/rc0_ackn
add wave -noupdate -expand -group mgr -label rst_n  -radix hex /xdrs/mgr_0/rc0_rstn
add wave -noupdate -expand -group mgr -label isol_n -radix hex /xdrs/mgr_0/rc0_reconfn

add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/rc_start
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/rc_bop
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/rc_done
add wave -noupdate -expand -group icapi -radix ascii /xdrs/icapi_0/state_ascii

add wave -noupdate -expand -group mem -label addr   -radix hex /xdrs/mem_0/xbs_addr
add wave -noupdate -expand -group mem -label rdwrn  -radix hex /xdrs/mem_0/xbs_rnw
add wave -noupdate -expand -group mem -label data_i -radix hex /xdrs/mem_0/xbs_data
add wave -noupdate -expand -group mem -label data_o -radix hex /xdrs/mem_0/sl_data

add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cclk
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/ccs_n
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cwe_n
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cdata
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cbusy
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cdata_rb

add wave -noupdate -expand -group region_IO(isolated) -label producer_ready -radix hex /xdrs/pc_0_prdy
add wave -noupdate -expand -group region_IO(isolated) -label consumer_ready -radix hex /xdrs/rr_0_crdy
add wave -noupdate -expand -group region_IO(isolated) -label consumer_error -radix hex /xdrs/rr_0_cerr
add wave -noupdate -expand -group region_IO(isolated) -label data -radix hex /xdrs/pc_0_data

add wave -noupdate -expand -group region_IO(not_isolated) -label producer_ready -radix hex /xdrs/region_0/c_prdy
add wave -noupdate -expand -group region_IO(not_isolated) -label consumer_ready -radix hex /xdrs/region_0/c_crdy
add wave -noupdate -expand -group region_IO(not_isolated) -label consumer_error -radix hex /xdrs/region_0/c_cerr
add wave -noupdate -expand -group region_IO(not_isolated) -label data -radix hex /xdrs/region_0/c_data

add wave -noupdate -expand -group module_A(max) -expand -group io -radix hex /xdrs/region_0/rm0/clk
add wave -noupdate -expand -group module_A(max) -expand -group io -label producer_ready -radix hex /xdrs/region_0/rm0/c_prdy
add wave -noupdate -expand -group module_A(max) -expand -group io -label consumer_ready -radix hex /xdrs/region_0/rm0/c_crdy
add wave -noupdate -expand -group module_A(max) -expand -group io -label data -radix hex /xdrs/region_0/rm0/c_data
add wave -noupdate -expand -group module_A(max) -expand -group inter -radix ascii /xdrs/region_0/rm0/state_ascii
add wave -noupdate -expand -group module_A(max) -expand -group inter -radix hex /xdrs/region_0/rm0/data1
add wave -noupdate -expand -group module_A(max) -expand -group inter -radix hex /xdrs/region_0/rm0/data2

add wave -noupdate -expand -group module_B(rev) -expand -group io -radix hex /xdrs/region_0/rm1/clk
add wave -noupdate -expand -group module_B(rev) -expand -group io -label producer_ready -radix hex /xdrs/region_0/rm1/c_prdy
add wave -noupdate -expand -group module_B(rev) -expand -group io -label consumer_ready -radix hex /xdrs/region_0/rm1/c_crdy
add wave -noupdate -expand -group module_B(rev) -expand -group io -label data -radix hex /xdrs/region_0/rm1/c_data
add wave -noupdate -expand -group module_B(rev) -expand -group inter -radix ascii /xdrs/region_0/rm1/state_ascii
add wave -noupdate -expand -group module_B(rev) -expand -group inter -radix hex /xdrs/region_0/rm1/data1
add wave -noupdate -expand -group module_B(rev) -expand -group inter -radix hex /xdrs/region_0/rm1/data2

# start simulation & state spy
onfinish stop; onbreak {resume}

profile on -p
profile on -m

run 10ns
add wave -noupdate -expand -group mgr //solyr/rr0/mon/usr_trans
add wave -noupdate -expand -group icap -expand //solyr/rr0/mon/sbt_trans
run -all

profile report -structural
profile report -du
