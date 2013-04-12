
.main clear; quit -sim; do settings.do;

# create libraries
if { [file exists elaborate] } { file delete -force ./elaborate }; file mkdir ./elaborate;
if { [file exists work] } { file delete -force ./work }; vlib work;
if { [file exists mtiReSim] } { file delete -force ./mtiReSim }; vlib mtiReSim;

echo ""
echo "===================================="
echo "== Compiling source code ..."
echo "===================================="
echo ""

# compile micro-processor system
do board_rtl.do
vlog +define+SYSTEM_IMPLEMENTATION -sv -f board_tb.f

# compile ReSim
vlog -work mtiReSim +acc "$RSV_HOME/src/rsv_ifs.sv"
vlog -work mtiReSim +acc +incdir+$RSV_HOME/src+$OVM_HOME/src "$RSV_HOME/src/rsv_solyr_pkg.svp"
vlog -work mtiReSim +acc "./artifacts/usr_ifs.sv"
vlog -work mtiReSim +acc +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src "./artifacts/usr_solyr_pkg.svp"

# compile artifacts
vlog +acc -work xps_math_v1_01_a +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/math_core.sv"
vlog +acc -work xps_icapi_v1_01_a +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/icap_virtex_wrapper.sv"
vlog +acc -work work +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim "./artifacts/my_solyr.sv"

echo ""
echo "===================================="
echo "== Running Simulation ..."
echo "===================================="
echo ""

vsim \
	-t ps -novopt +notimingchecks +nowarnTFMPC +nowarnPCDPC -suppress 4025,6610,3834 \
	-permit_unmatched_virtual_intf \
	-L work -L mtiReSim -L secureip -L unisims_ver -L simprims_ver -L XilinxCoreLib_ver work.board work.glbl

# load software program into BRAM/DDR2
#=====================================
#    BRAM: init & rfi to DDR2 0x10000 (extracted from hellow_word_0.elf)
#    DDR2: tapp_dpr_0_sim.elf + simulation-only bitstreams

exec ./tb/data2mem -bx ./ -u -i -bm ./tb/ddr2_256m.bmm -bd ../sdk/tapp_dpr_0/Debug/tapp_dpr_0_sim.elf
exec perl ./tb/edit_mem.pl ddr2_sdram_0_0.mem ddr2_sdram_0_1.mem ddr2_sdram_0_2.mem ddr2_sdram_0_3.mem
exec objdumpppc -D ../sdk/tapp_dpr_0/Debug/tapp_dpr_0_sim.elf > ./ddr2_sdram_elf.txt
file copy -force -- ../sdk/tapp_dpr_0/Debug/tapp_dpr_0_sim.elf ./ddr2_sdram.elf
file copy -force -- ./tb/bram_0_combined.hello_word.0.mem ./bram_0_combined_0.mem
file copy -force -- ./tb/bram_0_combined.hello_word.1.mem ./bram_0_combined_1.mem

when -label l_loading_ddr2_memory "/board/system/ppc440_0_PPC440MC_MCMIADDRREADYTOACCEPT == 1" {

	# note: memory endian (!!!! be very very careful !!!!)
	#
	#    ppc is bigendian, whereas the data2mem utility only support little endian
	#    so, we load the memory in REVERSE order as an turn-around method for memory data
	#    more specifically, ddr2_sdram_0_3.mem goes to /board/ddr2_0/memory

	echo "Loading software into DDR2 memory files (ddr2_sdram_0_x.mem) @ $now ps ... "
	mem load -infile ./ddr2_sdram_0_3.mem -format hex -filltype value -fillradix hex -filldata 0 /board/ddr2_0/memory
	mem load -infile ./ddr2_sdram_0_2.mem -format hex -filltype value -fillradix hex -filldata 0 /board/ddr2_1/memory
	mem load -infile ./ddr2_sdram_0_1.mem -format hex -filltype value -fillradix hex -filldata 0 /board/ddr2_2/memory
	mem load -infile ./ddr2_sdram_0_0.mem -format hex -filltype value -fillradix hex -filldata 0 /board/ddr2_3/memory

	# note: memory endian (!!!! be very very careful !!!!)
	#
	#    bitstream is bigendian endian, they are written directly to the ICAP, 
	#    so I just load the original bitstream data

	echo "Loading bitstream data into DDR2 memory files (ddr2_bankx.txt) @ $now ps ... "
	mem load -infile ./artifacts/sbt/ddr2_bank0.txt -format hex /board/ddr2_0/memory
	mem load -infile ./artifacts/sbt/ddr2_bank1.txt -format hex /board/ddr2_1/memory
	mem load -infile ./artifacts/sbt/ddr2_bank2.txt -format hex /board/ddr2_2/memory
	mem load -infile ./artifacts/sbt/ddr2_bank3.txt -format hex /board/ddr2_3/memory

	nowhen l_loading_ddr2_memory
}

do wave_mti.do

run 10ns
add wave -group icapctrl -group icap sim:/solyr/rr0/rec/sbt_trans

run -all
