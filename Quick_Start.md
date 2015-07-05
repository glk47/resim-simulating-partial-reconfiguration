# Quick Start #

This wiki page explains the steps of running the examples released along with the `ReSim` library (Release 2.3b). For an overview of the `ReSim` library, please refer to the [ReSim Overview](ReSim.md) page.



## System Requirements ##

ReSim is implemented using SystemVerilog and OVM library. It has been tested using QuestaSim/ModelSim 6.5g on Windows XP Professional SP2 machine and should work on other platforms. The tool also require Tcl 8.4 (or later) and Python 2.5 (or later).

The `State Migration` example requires EDK and has only been tested on EDK 12.4.

## Running Examples ##

The library includes 3 examples: XDRS, Fast PCIe configuration, and State Migration. The XDRS example further include three versions: XDRS.QUICKSTART XDRS.SINGLE XDRS.MULTIPLE. It is recommended that you run these examples in the following order:

  * XDRS.QUICKSTART
> > This example demonstrates the minimal effort to use ReSim.

  * XDRS.SINGLE
> > This example demonstrates the advanced concepts of ReSim. The concepts include, modifying artifacts for test-specific purposes (e.g. monitor, error injection) and using coverage-driven verification on DRS designs.

  * XDRS.MULTIPLE
> > This example demonstrates the use of ReSim on designs that have multiple reconfigurable regions.

  * Fast PCIe configuration
> > This example demonstrates the use of ReSim on a Xilinx reference design.

  * State Migration
> > This example demonstrates using ReSim to simulate a processor-based design with EDK tools. It also demonstrates designing and simulating a system that aesses module state (FFs, memory cells) via the configuration port.

## XDRS.QUICKSTART ##

This example demonstrates using ReSim in an in-house design, the XDRS demonstration platform. To focus on verification issues, the design is simplified in the release. In particular, the reconfigurable modules and the configuration controller are coded using synthesizable RTL style whereas the static part of the design is modeled using cycle-accurate behavioral code. This example illustrates the MINIMAL effort required by the user to use ReSim. The directory structure of the XDRS.QUICKSTART is illustrated below.

```
./artifacts ---------- // ReSim generated artifacts
./artifacts/sbt ------ // Simulation-only bitstreams (.sbt)
./artifacts/spy ------ // Logic allocation files (.sll)
./artifacts/synth ---- // RM wrappers that could be used for synthesis
./mtiReSim ----------- // Compiled ReSim library
./work --------------- // Compiled design & test library
./xdrs --------------- // XDRS design files
./xdrs/cores --------- // XDRS reconfigurable modules
./xtests ------------- // Testbench and tests
```

### The XDRS system ###

  * The XDRS application. The XDRS runs a producer-consumer application, in which the Producer-Consumer module (`./xdrs/prodcons.sv`) communicates with the RMs (`./xdrs/cores/maximum.v` & `./xdrs/cores/reverse.v`) to perform mathematical computation. Upon reconfiguration is requested, the RM block the request until it finishes the current data processing opertation (`./xdrs/cores/intern_sync.v` & `./xdrs/cores/filter_sync.v`).

![http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_gc_xdrs.jpg](http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_gc_xdrs.jpg)

  * The reconfiguration machinery. Reconfiguration machinery include all logic that _enables_ partial reconfiguration. The reconfiguration machinery (darkly shaded blocks in the figure) of the design is composed of the `ICAP-I` reconfiguration controller (`./xdrs/icapi.v`), the `SyncMgr` module (`./xdrs/manager.sv`) and the `Isolation` module (`./xdrs/isolator.v`). BEFORE reconfiguration, as listed in the specification, reconfiguration requests are blocked (not acknowledged) until the RM becomes idle. DURING reconfiguration, the `Isolation` module drives default values to the static region and isolates the RR undergoing reconfiguration. On the other hand, the `ICAP-I` controller transfers a partial bitstream to the ICAP. AFTER reconfiguration, the newly configured module is reset to IDLE by the `SyncMgr` module.

  * The system backplane (memory and bus). Both bitstream data and application data (i.e., data accessed by RMs) are stored in the same memory (./xdrs/memctrl.sv). During reconfiguration, a bus abiter (`./xdrs/xbuscore.v`) schedules the two traffic streams, where the application traffic has a higher priority.

  * The test(s). Tests are "included" as part of the top-level testbench (`./xdrs/xdrs.sv`). This example only has one test (`./xtests/tdpr_quick_start.sv`), which performs two reconfiguration operations. The partial bitstreams for the `maximum` and the `reverse` module are loaded at memory address 0x100 and 0x200.

```

// ./tdpr_quick_start.sv
// ============================
// This file is manually created

// Starting test and setting verbosity level
initial begin
    #1
    ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_QUICK_START");
    ovm_top.set_report_verbosity_level_hier(OVM_FULL);
    #80_000 $finish();
end

// Producer-consumer thread
// Producing data by calling pc_0.produce_data()
initial begin
    pc_0.produce_data(32'ha4a5a6a7);
    pc_0.produce_data(32'ha0a1a2a3);
        
        
// Partial reconfiguration thread
// Performing partial reconfiguration by calling mgr_0.reconfigure_module()
// The partial bitstream for the maximum module is loaded at address 0x100 and the size is 32 words. 
// Note, the bitstream address and size should match the ones specified in the parameter script
initial begin
    mgr_0.reconfigure_module(8'b0000_0001, 32'h100, 32);

```

### Generating simulation-only artifacts ###

Create a `settings.do` file in the working folder. This file is required to setup directory pathes. Here is an example of the file.

```

// ./settings.do 
// ============================
// This file must be added by the user in order to run the example
// The following is an example of the settings.do file

set RSV_HOME "C:/DPR_TOOLS/ReSim"
set OVM_HOME "C:/ModelSim6.5g/verilog_src/ovm-2.1.1"
source "$RSV_HOME/scripts/resim.do"
```

Run `auto_generation.tcl`. This step automatically generates simulation-only artifacts that should be included in the simulation testbench. The designers need to create such Tcl script for their projects. Here are selected lines of the parameter script.

```

// ./auto_generation.tcl
// ============================
// This file is manually created
// The parameter script for XDRS.QUICKSTART

source settings.do; // Setup library path
namespace import ReSim::* // Import ReSim library

rsv_create_portmap "my_if" "clk" // Create a portmap and add ports to it.
rsv_add_port "my_if" "rstn" in
...

rsv_create_region "my_region" "my_if" 4 "" "my_ei" // Create reconfigurable regions and add modules to it.
rsv_add_module "my_region" "maximum" ""
...

rsv_create_solyr "my_solyr" VIRTEX4 "" // Create the simulation-only layer and add reconfigurable regions to it.
rsv_add_region   "my_solyr" "my_region"
rsv_gen_solyr    "my_solyr" // Generate the simulation-only layer
...

```

The generated SimB are in binary format (See ./artifacts/sbt/xxxx.sbt) and can not be used by the ModelSim simulator directly. The `rsv_create_memory` and the `rsv_add_2_memory` APIs convert the binary SBT into a "memory format" that are ready to be loaded into ModelSim. In this example, the memory is a word-addressable, single bank memory (see `./xdrs/memctrl.sv`), and the two SimBs are loaded to address 0x100 and 0x200 respectively.

Note, the conversion of SimB is optional. The designer can create their own script to convert binary format SimB to whatever format that meets can be understood by the simulation environment.

```

// ./xdrs/memctrl.sv
// ============================
// This file is manually created
// The bitstream storage memory 

module memctrl 
    ...
    reg [31:0] zbtmem [0:4095]; // 32-bit addressable, 4096 entries. 
    ...
endmodule

// ./auto_generation.tcl (con't)
// ============================
// This file is manually created
// The parameter script for XDRS.QUICKSTART

rsv_create_memory "zbt" 4 1 be // Convert SimB to ModelSim memory format

rsv_add_2_memory "zbt" "./artifacts/sbt/my_region_rm0.sbt" 0x100
rsv_add_2_memory "zbt" "./artifacts/sbt/my_region_rm1.sbt" 0x200

```

Running the `auto_generation.tcl` script generates the `./artifacts` folder.

### Simulation Results ###

In this example, all steps required to use the artifacts have already been done. Simply start ModelSim in the root directory of the example.
```
ModelSim> do simulate_mti.do
```

The following figure is a screen shot of the simulating XDRS.QUICKSTART. You can see that the maximum module is active at the beginning. At about 20ms, a SimB is transferred to the ICAP port (see the toggling of the ICAP signals). During reconfiguration, both modules are inactive (see the undefined X values of both modules). After reconfiguration, the reverse module is reset to IDLE.

![http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_gc_xquickstart.jpg](http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_gc_xquickstart.jpg)

### Using the simulation-only artifacts ###

For your own project, you have to integrate the generated artifacts into your simulation environment yourself. **To assist in such integration, ReSim automatically generates a TODO list in `./artifacts/my_solyr_todolist.txt`, which provides useful templates to get you started with the integration.** This wiki page explains required steps as follow.

The generated artifacts needs to be instantiated in your design and your artifacts. **Firstly**, you need to instantiate the wrapper module for the reconfigurable region(s) in the static design. This example only has one region `my_region` (`./artifacts/my_region.sv`). The wrapper is a place holder that instantiates and interleaves both reconfigurable modules (i.e., `maximum` & `reverse`).
The wrapper module itself is instantiated as a sub-module of the static region.

```

// ./artifacts/my_region.sv 
// ============================
// This file is automatically generated
// Instantiate the two reconfigurable modules

maximum  rm0 (
    .clk              ( rm0_rif.clk              ),
    .rstn             ( rm0_rif.rstn             ),
    ...
);

reverse  rm1 (
    .clk              ( rm1_rif.clk              ),
    .rstn             ( rm1_rif.rstn             ),
    ...
);

// ./xdrs/xdrs.sv 
// ============================
// This file is manually created
// Instantiate the wrapper module for the reconfigurable region

// Note, the design hierarchy is 
// xdrs: xdrs
//   region_0: my_region // One additional level of design hierarchy
//     rm0: maximum
//     rm1: reverse

my_region region_0 (
    .clk              (rc0_clk            ),
    .rstn             (rc0_rstn           ),
...

```

Since the wrapper module for the reconfigurable region is a simulation-only artifact, it should not be included in synthesis. ReSim automatically generates the implementation version of the wrapper module for synthesis purposes. Using these files, the user can implement the DRS design using vendor tools such as PlanAhead.

```

// ./artifacts/synth/my_region_rm0.v 
// ============================
// This file is automatically generated
// Instantiate the maximum module
// Should be used as the top-level for synthesizing the maximum module

maximum  rm (
    .clk              ( clk              ),
    .rstn             ( rstn             ),
    ...
);

// ./artifacts/synth/my_region_rm1.v 
// ============================
// This file is automatically generated
// Instantiate the reverse module
// Should be used as the top-level for synthesizing the reverse module

reverse  rm (
    .clk              ( clk              ),
    .rstn             ( rstn             ),
    ...
);

// ./artifacts/synth/my_region_rm0_bb.v 
// ./artifacts/synth/my_region_rm1_bb.v 
// ============================
// These two files are automatically generated
// A black box for the reconfigurable modules
// Should be used as a placeholder for synthesizing the static region

(* BOX_TYPE = "BLACK_BOX" *)
module my_region
(
    input           clk             ,
    input           rstn            ,
    ...
);

endmodule

```

**Secondly**, you need to instantiate the ICAP port in your design. A typical DRS would instantiate the ICAP primitive as part of the design. In order to use ReSim, you have to instantiate the ReSim-generated ICAP instead of the ICAP primitive of Xilinx.

```
// ./xdrs/icapi.v 
// ============================
// This file is manually created
// Instantiate the ICAP

ICAP_VIRTEX4_WRAPPER #("X32") icap_0 (
    .CLK         (clk                ),
    .CE          (cfg_cen            ),
    .WRITE       (cfg_wen            ),
    .I           (cfg_data           ),
    .O           (cfg_rdbk_i         ),
    .BUSY        (cfg_busy           )
);
```

ReSim automatically generates two versions of the `ICAP_VIRTEX4_WRAPPER`, one for implementation and one for simulation. By using the two versions of the same module, users only need to change the compilation script to switch between implementation and simulation.

```
// ./artifacts/synth/icap_virtex_wrapper.vhd
// ============================
// This file is automatically generated
// The implementation version of the ICAP_VIRTEX4_WRAPPER

entity ICAP_VIRTEX4_WRAPPER is
    /* ... */
end ICAP_VIRTEX4_WRAPPER;

architecture synth of ICAP_VIRTEX4_WRAPPER is 
    /* Instantiate the ICAP primitive from Xilinx */
end synth;

// ./artifacts/icap_virtex_wrapper.sv
// ============================
// This file is automatically generated
// The simulation version of the ICAP_VIRTEX4_WRAPPER

module ICAP_VIRTEX4_WRAPPER is
    /* Code for simulation version of ICAP */
endmodule;

```

**Thirdly**, you need to instantiate the simulation-only layer. Since ReSim is implemented by OVM, the simulation-only layer can be instantiated anywhere in the testbench and it can automatically be "connected" with the ICAP artifact and the reconfigurable region wrapper module. Note the name of the simulation-only layer should match the one specified in the parameter script (the `rsv_create_solyr` API). In this example, the simulation-only layer is instantiated in the top-level testbench.

```

// ./xdrs/xdrs.sv 
// ============================
// This file is manually created
// Instantiate the simulation-only layer
// NO parameter required, NO IO signals required

my_solyr sol_0(); 

```

**The next step** is to compile the generated artifacts. The compilation script can be found in the `./simulate_mti.do` file. For your own project, simply cut and paste the compilation script in `./artifacts/my_solyr_todolist.txt` into the ModelSim prompt and execute them one by one.

```

ModelSim> source settings.do
ModelSim> vlib mtiReSim

// Compile the ReSim library and the generated artifacts
// This part is the same for all projects
ModelSim> vlog -work mtiReSim $RSV_HOME/src/rsv_ifs.sv
ModelSim> vlog -work mtiReSim +incdir+$RSV_HOME/src+$OVM_HOME/src $RSV_HOME/src/rsv_solyr_pkg.svp
ModelSim> vlog -work mtiReSim ./artifacts/usr_ifs.sv
ModelSim> vlog -work mtiReSim +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src ./artifacts/usr_solyr_pkg.svp

// Compile the ReSim library and the generated artifacts
// This part varies for different projects
ModelSim> vlog +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim ./artifacts/my_region.sv
ModelSim> vlog +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim ./artifacts/icap_virtex_wrapper.sv
ModelSim> vlog +incdir+./artifacts+$RSV_HOME/src+$OVM_HOME/src -L mtiReSim ./artifacts/my_solyr.sv

```

**The last step** is to run simulation using the `vsim` command. Remember to add two more options on top off other simulation options. Also remember to load the SimB into the memory before running simulation.

```
ModelSim> vsim -L mtiReSim -permit_unmatched_virtual_intf $MY_TEST

ModelSim> mem load -filltype value -fillradix hex -filldata 0 /xdrs/mem_0/zbtmem; // Fill the memory with zero
ModelSim> mem load -infile ./artifacts/sbt/zbt_bank0.txt -format hex /xdrs/mem_0/zbtmem // Load the memory with SimB

ModelSim> run -all

```

### Summary ###

To use ReSim, the designer needs to create a parameter script to generate artifacts, and to integrate the generated artifacts with the design-specific simulation environment. The designer can then view and debug the partial reconfiguration process in ModelSim.

## XDRS.SINGLE ##

This example demonstrates the advanced concepts of ReSim. The concepts include, modifying artifacts for test-specific purposes (e.g. error injection) and using coverage-driven verification on DRS designs.

### The XDRS system ###

The Design Under Test (DUT) of this example is exactly the same as the XDRS.QUICKSTART example. However, this example includes more tests (see `./xtests`). These tests examine various aspects of the XDRS system.

### Generating simulation-only artifacts ###

Same as the XDRS.QUICKSTART example, you need to create a `settings.do` file indicating the directory path for ReSim.

The parameter script for this example is also similar to the one in the XDRS.QUICKSTART example. However, instead of the default error\_injector, this example modifies the default one (`./artifacts/my_ei_edited.sv`). It also uses a scoreboard (`./artifacts/my_scb.sv`).

```

// ./auto_generation.tcl
// ============================
// This file is manually created

// Create the reconfigurable region and add modules
// Attach an error_injector to the region
// Pass non-default parameter values to reconfigurable modules

rsv_create_region "my_region" "my_if" 4 "" "my_ei_edited"
rsv_add_module "my_region" "maximum" "#(48)"
rsv_add_module "my_region" "reverse" "#(24,24)"

// Create the simulation-only layter and attach a scoreboard to it

rsv_create_solyr "my_solyr" VIRTEX4 "my_scb"

```

This example modifies the generated artifacts for test purposes. **The general steps for modifying the artifacts can be found in steps 5,6,7 of the generated TODO list file (`./artifacts/xxx_todolist.txt`). Modification is only required are for advanced users who wish to change the default artifacts for test purposes.** In this example, the modified artifacts are in the `./artifacts.edited` folder and they are all copied to overwrite the default artifacts by the Tcl script.

The error\_injector (`./artifacts/my_ei_edited.sv`) has been derived and overridden so that it can _inject_ design-specific errors to mimic suprious RM outputs and undifined RM state. In particular, the `inject_to_static_module` task and the `inject_to_reconfigurable_module` task drives errors to IO signals of the static region and the reconfigurable module respectively. The `inject_to_internal_signals` task forces internal signals of the RM to be either zero, X or random value.

```

// ./artifacts/my_ei_derived.sv
// ============================
// This file is automatically generated and then modified manually

// Use the auto-generated inject_to_static_module task
// Inject undefined X to the ***outputs*** to the static region 
// Use the ei_vi interface to enable/disable error injection
// Use the sei_vi interface to drive signals of the static region

task my_ei_edited::inject_to_static_module ();
    ei_vi.sei_en <= 1;
    ...
    sei_vi.rc_ackn          <= x;
    sei_vi.p_prdy           <= x;
    ...
endtask : my_ei_edited::inject_to_static_module

// Define the design-specific inject_to_reconfigurable_module task
// Inject design-specific errors to the ***inputs*** to the RM
// Use the ei_vi interface to enable/disable error injection
// Use the dei_vi interface to drive signals of the RM

task my_ei_edited::inject_to_reconfigurable_module ();
    ei_vi.dei_en <= 1;
    ...
endtask : my_ei_edited::inject_to_reconfigurable_module

// Define the design-specific inject_to_internal_signals task
// Inject design-specific errors to the ***internal signals*** of the RM
// Use the Tcl API "rsv_iei_hdl_state" to perform internal error injection
// Use the "rsv_execute_tcl" macro to execute/evaluate the Tcl API in the ModelSim kernel (i.e., the Tcl interpreter)
// Users can add code to evaluate other ModelSim commands (e.g., force, mem load) to inject errors 

task my_ei_edited::inject_to_internal_signals ();
    ...
    rsv_execute_tcl(interp, $psprintf("ReSim::rsv_iei_hdl_state %s rm%0d x rand",rr_inst,old_rmid))
endtask : my_ei_edited::inject_to_internal_signals
```

This example also include two user-defined tasks that are used by other error injection tasks.

```
task my_ei_edited::ei_reset_rm ();
    // Munipulate signals of the RM to ***generate*** a reset sequence
    ...
endtask : my_ei_edited::ei_reset_rm

task my_ei_edited::ei_inject_to_rm (logic [31:0] ei_data);
    // Munipulate signals of the RM to ***inject*** ei_data to the RM
    ...
endtask : my_ei_edited::ei_inject_to_rm
```

The logic allocation files (`./artifacts/spy/xxx.sll`) has been modified so as to map RTL signals to the configuration data section of the SimB. The logic allocation files are used by the configuration readback test (`tdpr_demo.sv & tdpr_readback.sv`)

```

// ./artifacts/spy/my_region_rm0.sll
// ============================
// This file is automatically generated and then modified manually
// The data1 signal is allocated to frame_address = 0x00000000, offset = 32, bitwith = 32. 

0x00000000 32 32 data1
...

```

### Running a Single Test ###

Open `simulate_mti.do` and change the name of the test to be compiled (line 34). For example, to run the random test (`./xtests/tdpr_random.sv`), change the test name to

```
vlog ..... +define+TEST_DPR_RANDOM "./xdrs/xdrs.sv"
```

Valid tests include:

  * `TEST_DPR_SIMPLE`: A simple test that performs two partial reconfiguration operations. For the 2nd partial reconfiguration, a high priority memory traffic occurs on the shared bus and the bitstream traffic is thereby delayed.
  * `TEST_DPR_READBACK`: A test that performs configuration readback and state restoration. In particular, the registers of the `maximum` module (as specified by the `./artifacts/spy/my_region_rm0.sll` file) is saved and restored by reading and writing the configuration port.
  * `TEST_DPR_ISOLATION` and `TEST_DPR_RETRY`: Two tests that exercise corner cases of the `Isolation` module.
  * `TEST_DPR_RANDOM`: A test that drives random stimuli to the XDRS.
  * `TEST_DPR_DEMO`: A test that is a mixture of all above tests. It is used for demonstration purposes.

Start ModelSim in the working directory type in the prompt

```
ModelSim> do simulate_mti.do
```

### Running all Tests and Analyzing Test Coverage ###

This example also illustrates coverage analysis. The starting point of coverage analysis is a testplan, which lists all test scenarios that need to be exercised. The following figure shows a section of the testplan of XDRS (see `./testplan.xml` for the complete testplan).

![http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_gc_xcov.jpg](http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_gc_xcov.jpg)

The testplan includes code coverage items, which are automatically tracked by the simulator, and functional coverage items, which are manually modeled using SystemVerilog coverage groups, coverage directives and assertions. We illustrate the modeling of DPR-related coverage items as follows.

```

// ./xdrs/xdrs.sv
// ============================
// This file is manually created
// Coverage directive modeling item 5.4 of the testplan
// Cover the scenario that during reconfiguration (~rc0_reconfn), the static region requests for computational requests (pc_0_prdy)

cov_isolator_cancel_static : cover property (@(posedge clk) ~rc0_reconfn && pc_0_prdy);

// ./xdrs/cores/maximum.v
// ============================
// This file is manually created
// Coverage directive modeling item 6.6 of the testplan
// Reconfiguration can only be acknowledged when IDLE
// The corner case is to acknowledge and start computation at the same time

assert_maximum_cfg_ack : assert property (@(posedge clk) disable iff(~rstn)
    
    // The acknowledge of reconfiguration (~rc_ackn) implies that 
    // the current FSM state (state_c) is IDLE
    
    (~rc_ackn) |-> (state_c == S_IDLE)
);

// ./artifacts/my_region.sv
// ============================
// This file is automatically created
// Coverage group modeling item 7.2 of the testplan
// The coverage group tracks the current module id to sample the transition between modules. 

covergroup cvg_my_region_drp @pif.active_module_id;
    ...

    // Generate 4 bins covering all possible transitions
    // Ignoring the case when a same module is reconfigured

    module_transition: coverpoint pif.active_module_id {
        bins cfg[] = ([0:1] => [0:1]);
        ignore_bins cfg_no_change = (0=>0),(1=>1);
        illegal_bins other = default sequence;
    }
    ...
endgroup

```

The coverage items are embedded in the design source and tracked in simulation. Start ModelSim in the working directory and run all tests:

```
ModelSim> do simulate_coverage.do
```

After simulating all tests, the coverage data of all tests are merged to a single database (`./coverage/merged.ucdb`) and are ranked according to their contribution to the accumulated coverage (`./coverage/merged.rank`). The coverage data can be viewed in ModelSim as illustrated in the above figure. In particular, coverage data are reported according to the sections of the testplan (see the left half of the ModelSim screen shot). For this example, the accumulated coverage are 100% for all sections.

ModelSim also generates an HTML coverage report (`./coverage/covhtmlrpt/index.html`), which compares the test results with the testplan. You can view the report using an Internet browser.

### Summary ###

For advanced users, the designer can optionally modify the generated artifacts. The error injector can be modified to inject design-specific error sequences. The logic allocation files can be modified to map RTL signals to the configuration memory of the simulation-only layer.

Using ReSim, the designer apply coverage-driven verification to the design. In particular, the designer need to create a testplan, model the testplan into trackable coverage items in the design source code, and run simulation.

## XDRS.MULTIPLE ##

This example demonstrates the use of ReSim on designs that have multiple reconfigurable regions. In particular, the XDRS system now has 3 reconfigurable regions. RR0 & RR1 contains the `maximum` & `reverse` modules that are the same as previous examples but with different parameters, whereas RR2 is mapped with two low pass filters (`./xdrs/lpfilter/...`). Three regions have the same set of IO signals.

The filters use a `pipeline_sync` module ((`./xdrs/lpfilter/pipeline_sync.v`) to perform synchronization. In particular, upon a reconfiguration is requested, the `pipeline_sync` module blocks the request and push zeros to the filter to flush the data that are still in the filter. Reconfiguration is acknowledge after all data are flushed out of the filter.

### Running a Single Test ###

Generate the artifacts by running the parameter script (`./auto_generation.tcl`). Open `simulate_mti.do` and change the name of the test to be compiled (line 41). For example, to run the random test (`./xtests/tdpr_random.sv`), change the test name to

```
vlog ..... +define+TEST_DPR_RANDOM "./xdrs/xdrs.sv"
```

This example has two tests:

  * `TEST_DPR_STREAMING`: This test reconfigures RR2 (i.e., the filter) twice.
  * `TEST_DPR_RANDOM`: A test that drives random stimuli to the XDRS.

### Summary ###

This example demonstrates the use of ReSim on designs that have multiple reconfigurable regions. The regions can have same or different reconfigurable modules. The general steps of using ReSim are the same for single and multiple region DRS.