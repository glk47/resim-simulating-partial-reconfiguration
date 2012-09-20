#  Simulation Model Generator
#  Xilinx EDK 12.4 EDK_MS4.81d
#  Copyright (c) 1995-2010 Xilinx, Inc.  All rights reserved.
#
#  File     system.do (Wed Jun 15 23:40:35 2011)
#

global XILINX_HOME
global XLIB_HOME

vmap proc_sys_reset_v3_00_a "$XLIB_HOME/edk/proc_sys_reset_v3_00_a/"
vmap clock_generator_v4_01_a "$XLIB_HOME/edk/clock_generator_v4_01_a/"
vlib "./elaborate/clock_generator_0_v4_01_a"; vmap clock_generator_0_v4_01_a "./elaborate/clock_generator_0_v4_01_a"
vmap ppc440_virtex5_v1_01_a "$XLIB_HOME/edk/ppc440_virtex5_v1_01_a/"
vmap ppc440mc_ddr2_v3_00_c "$XLIB_HOME/edk/ppc440mc_ddr2_v3_00_c/"
vmap jtagppc_cntlr_v2_01_c "$XLIB_HOME/edk/jtagppc_cntlr_v2_01_c/"
vmap proc_common_v3_00_a "$XLIB_HOME/edk/proc_common_v3_00_a/"
vmap plb_v46_v1_05_a "$XLIB_HOME/edk/plb_v46_v1_05_a/"
vmap plbv46_master_v1_04_a "$XLIB_HOME/edk/plbv46_master_v1_04_a/"
vmap plbv46_master_burst_v1_01_a "$XLIB_HOME/edk/plbv46_master_burst_v1_01_a/"
vmap plbv46_slave_v1_04_a "$XLIB_HOME/edk/plbv46_slave_v1_04_a/"
vmap plbv46_slave_single_v1_01_a "$XLIB_HOME/edk/plbv46_slave_single_v1_01_a/"
vmap plbv46_slave_burst_v1_01_a "$XLIB_HOME/edk/plbv46_slave_burst_v1_01_a/"
vmap interrupt_control_v2_01_a "$XLIB_HOME/edk/interrupt_control_v2_01_a/"

vmap xps_intc_v2_01_a "$XLIB_HOME/edk/xps_intc_v2_01_a/"
vmap xps_uartlite_v1_01_a "$XLIB_HOME/edk/xps_uartlite_v1_01_a/"
vmap sysace_common_v1_01_a "$XLIB_HOME/edk/sysace_common_v1_01_a/"
vmap xps_sysace_v1_01_a "$XLIB_HOME/edk/xps_sysace_v1_01_a/"
vmap xps_bram_if_cntlr_v1_00_b "$XLIB_HOME/edk/xps_bram_if_cntlr_v1_00_b/"
vlib "./elaborate/bram_0_elaborate_v1_00_a"; vmap bram_0_elaborate_v1_00_a "./elaborate/bram_0_elaborate_v1_00_a"

vlib work; vmap work work
vlib "./elaborate/ipif_v1_00_a"; vmap ipif_v1_00_a "./elaborate/ipif_v1_00_a"
vlib "./elaborate/simmodels_v1_00_a"; vmap simmodels_v1_00_a "./elaborate/simmodels_v1_00_a"
vlib "./elaborate/xps_icapi_v1_01_a"; vmap xps_icapi_v1_01_a "./elaborate/xps_icapi_v1_01_a"
vlib "./elaborate/xps_math_v1_01_a"; vmap xps_math_v1_01_a "./elaborate/xps_math_v1_01_a"

vcom -novopt -93 -work clock_generator_0_v4_01_a "./behavioral/elaborate/clock_generator_0_v4_01_a/hdl/vhdl/clock_generator.vhd"
vlog -novopt -work bram_0_elaborate_v1_00_a "./behavioral/elaborate/bram_0_elaborate_v1_00_a/hdl/verilog/bram_0_elaborate.v" {+incdir+./behavioral/elaborate/bram_0_elaborate_v1_00_a/hdl/verilog/+D:/Electronic/Xilinx/12.4/ISE_DS/EDK/hw/XilinxBFMinterface/pcores/+D:/Electronic/Xilinx/12.4/ISE_DS/EDK/hw/XilinxProcessorIPLib/pcores/}

vcom -novopt -93 -work ipif_v1_00_a "../edk/pcores/ipif_v1_00_a/hdl/vhdl/plbv46_master_burst_wrapper_128.vhd"
vcom -novopt -93 -work ipif_v1_00_a "../edk/pcores/ipif_v1_00_a/hdl/vhdl/plbv46_slave_burst_wrapper_128.vhd"
vlog -novopt -work xps_math_v1_01_a "../edk/pcores/xps_math_v1_01_a/hdl/verilog/soft_clock.v"
vcom -novopt -93 -work xps_math_v1_01_a "../edk/pcores/xps_math_v1_01_a/hdl/vhdl/user_logic.vhd"
vcom -novopt -93 -work xps_math_v1_01_a "../edk/pcores/xps_math_v1_01_a/hdl/vhdl/xps_math.vhd"
vlog -novopt -work xps_math_v1_01_a "../edk/pcores/xps_math_v1_01_a/partial/verilog/adder.v"
vlog -novopt -work xps_math_v1_01_a "../edk/pcores/xps_math_v1_01_a/partial/verilog/maximum.v"
vcom -novopt -93 -work xps_icapi_v1_01_a "../edk/pcores/xps_icapi_v1_01_a/hdl/vhdl/icap_wrapper.vhd"
vlog -novopt -work xps_icapi_v1_01_a -sv "../edk/pcores/xps_icapi_v1_01_a/hdl/verilog/icapi.v"
vlog -novopt -work xps_icapi_v1_01_a -sv "../edk/pcores/xps_icapi_v1_01_a/hdl/verilog/xbus_masterif.v"
vlog -novopt -work xps_icapi_v1_01_a "../edk/pcores/xps_icapi_v1_01_a/hdl/verilog/icapi_regs.v"
vlog -novopt -work xps_icapi_v1_01_a "../edk/pcores/xps_icapi_v1_01_a/hdl/verilog/xps_icapi_core.v"
vlog -novopt -work xps_icapi_v1_01_a "../edk/pcores/xps_icapi_v1_01_a/hdl/verilog/xps_icapi.v"

vcom -novopt -93 -work work "./behavioral/proc_sys_reset_0_wrapper.vhd"
vcom -novopt -93 -work work "./behavioral/clock_generator_0_wrapper.vhd"
vcom -novopt -93 -work work "./behavioral/ppc440_0_wrapper.vhd"
vlog -novopt -work work "./behavioral/ddr2_sdram_0_wrapper.v"
vcom -novopt -93 -work work "./behavioral/jtagppc_cntlr_0_wrapper.vhd"
vcom -novopt -93 -work work "./behavioral/plb_v46_0_wrapper.vhd"
vcom -novopt -93 -work work "./behavioral/xps_intc_0_wrapper.vhd"
vcom -novopt -93 -work work "./behavioral/xps_uart_0_wrapper.vhd"
vcom -novopt -93 -work work "./behavioral/xps_sysace_0_wrapper.vhd"
vcom -novopt -93 -work work "./behavioral/xps_bram_if_cntlr_0_wrapper.vhd"
vlog -novopt -work work "./behavioral/bram_0_wrapper.v"
vcom -novopt -93 -work work "./behavioral/xps_icapi_0_wrapper.vhd"
vcom -novopt -93 -work work "./behavioral/xps_math_0_wrapper.vhd"
vlog -novopt -work work "./behavioral/system.v"


