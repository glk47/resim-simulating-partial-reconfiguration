set str "This file briefly explains things you need to do after generating the code.
This file also contains source code (Tcl/HDL) that you may find useful when integrating 
ReSim to your exisisting testbench. The code in this file is just for your refernece. 

TODO 1: Before using any functions in the ReSim library, you must set the 
Tcl variable RSV_HOME & OVM_HOME, source the \"resim.do\" from your own script, e.g.

    set RSV_HOME \"C:/ReSim\"
    set OVM_HOME \"C:/ModelSim/verilog_src/ovm-2.1.1\"
    source \$RSV_HOME/scripts/resim.do

TODO 2: For compiling the SystemVerilog code of the genenrated artifacts, you can 
copy and paste the following scripts to your own Modelsim do script 

    vlib mtiReSim
    vlog -work mtiReSim \$RSV_HOME/src/rsv_ifs.sv
    vlog -work mtiReSim +incdir+\$RSV_HOME/src+\$OVM_HOME/src \$RSV_HOME/src/rsv_solyr_pkg.svp
    vlog -work mtiReSim ./artifacts/usr_ifs.sv
    vlog -work mtiReSim +incdir+./artifacts+\$RSV_HOME/src+\$OVM_HOME/src ./artifacts/usr_solyr_pkg.svp

[rsv_print_fpga $vf_ rr \n _vcom]
    vlog +incdir+./artifacts+\$RSV_HOME/src+\$OVM_HOME/src -L mtiReSim ./artifacts/icap_virtex_wrapper.sv
    vlog +incdir+./artifacts+\$RSV_HOME/src+\$OVM_HOME/src -L mtiReSim ./artifacts/$vf_.sv

TODO 3: For simulating the testbench, you need to turn on the \"permit_unmatched_virtual_intf\"
option so as to use the virtual interfaces, and to include the compiled library with \"-L mtiReSim\" 
For example, 

    vsim -L mtiReSim -permit_unmatched_virtual_intf \$MY_TEST
    
You also need to load the simulation-only bitstreams into the bitstream storage memory using the 
ModelSim command \"mem load\". Note, by default, the generated bitstreams are in binary format and 
you can use the \"rsv_create_memory\" and \"rsv_add_2_memory\" APIs to convert bitstreams into 
ModelSim memory format (see the released examples). Alternatively, you can create your own utilities 
to perform such conversion. 

    mem load -infile ./artifacts/sbt/xxx_bank0.txt -format hex \$DESIGN_HIERARCHY_TO_BITSTREAM_MEMORY
    mem load -infile ./artifacts/sbt/xxx_bank1.txt -format hex \$DESIGN_HIERARCHY_TO_BITSTREAM_MEMORY
    ...

TODO 4: To integrate the generated code into the HDL testbench, you need to instantiate 
the generated modules. More specifically you need to instantiate 3 types of modules 

(a) Instantiate the reconfigurable region(s) in a way same as normal module(s), e.g.,

    [lindex $rr_ 0] i_[lindex $rr_ 0] ( ... );

(b) Instantiate the ICAP port in a way same as normal module(s). e.g.,

    $cp_ #(\"X32\") i_$cp_ ( ... );

(c) Instantiate the simulation-only layer. The simulation-only layer was specified in
the auto-generation script, and is a module with no input or output. e.g.,

    ${vf_} i_sol();

Furthermore, you need to create test stimuli that performs partial reconfiguration. Typically, 
this involves transferring bitstreams from the bitstream storage memory to the configuration port.

TODO 5 (optional): For state spy, you need to create a logic allocation file (sll) specifying
the frame address of all hdl signals that are of interest to your verification. An empty sll 
file is automatically generated in ./artifacts/spy for each reconfigurable module. Users need 
to complete this sll file if you wish to simulate the state saving and restoration process 
of partial reconfiguration. For patially reconfiguring module logic, you can simply leave them
as empty files, but you can not delete or move them. The syntax of sll file is similar to 
its equivalent .ll file of Xilinx. For example, 
    
    0x0102000c 36 16 my_hdl_signal_0
    0x0102000c 52 32 my_sub_module/my_hdl_signal_1
    
The above two lines declares two signals that needs to be CAPTUREd and/or RESTOREd. The first
line means a signal called \"my_hdl_signal_0\" is allocated to frame address 0x0102000c, 
starting from bit offset 36, and has a bitwith of 16. Thus it occupies bit 36(LSB)-51(MSB) of that frame. 
The second example shows a signal in a sub-module, thus a path seperater / is used. The second
signal starts from bit offset 52 and occupies 32 bits of the frame. Each frame can hold up to
96 bits of HDL signals. The user must ensure that the allocation of all signals do not overlap.
The user should also ensure that each frame does not hold more than 96 bits of signals.

TODO 6 (optional): To virsualize transactions created by the scoreboard, add the following
commands to your script. Note the transaction streams (usr_trans & sbt_trans) are not created
until the simulation starts running for sometime. So you must delay, for example, 10ns BEFORE
adding the two streams to the wave window. 
The following commands are for the default reconfigurable region (rr0) in your design. 
If you have multiple reconfigurable regions feel free to substitute rr0 with rr1, rr2, etc.

    run 10ns
    add wave sim:/solyr/rr0/rec/usr_trans
    add wave sim:/solyr/rr0/rec/sbt_trans

TODO 7 (optional): To define your own error injector, you need to specify the name of the 
error injector when creating your reconfigurable region. e.g.,

    rsv_create_region \"[lindex $rr_ 0]\" ... \"\" YOUR_ERROR_INJECTOR
    
and add design specific code in the generated template file. Note, if you don't want to use 
error injection, please use \"\" as a place-holder when creating the reconfigurable region. 

    rsv_create_region \"[lindex $rr_ 0]\" ... \"\" \"\"
    
"

