# Reference Manual #

This wiki page describes the details of the implementation and APIs of the `ReSim` library (Release 2.3b). For a high-level description of the library, please refer to the [ReSim Overview](ReSim.md) page.



## Library Overview ##

The following figure illustrates ReSim-based RTL simulation of a DRS design. The ReSim library adopts the Open Verification Methodology (OVM) and, according to the reusability principle of OVM, the simulation-only layer is separated into a _module-based_ part and a _class-based_ part, which are connected via SystemVerilog Interfaces (shown as clouds and the _vi_ symbols). In particular, a ReSim-based simulation environment contains the following components:

  * The CP artifact: A CP wrapper, which is instantiated in the user design hierarchy as the configuration port, and a CP class, which controls the operation of the CP wrapper module (i.e., the `rsv_virtex_icap` class) and parses SimBs (i.e., the `rsv_sbt_parser` class).

  * The RR artifact: RR wrappers, which are instantiated in the user design hierachy as the top-level of the reconfigurable regions, and instances of RR classes, which controls module swapping (i.e., the `rsv_portal_controller` class), injects errors (i.e., the `rsv_error_injector` class), and maintains state of simulated RMs (i.e., the `rsv_state_spy` class).

  * The simulation-only layer artifact: A simulation-only layer wrapper, which is instantiated in the testbench as the module-based part of the simulation-only layer, and a simulation-only layer class (i.e., the `rsv_solyr` class), which instantiates all class-based artifacts.

  * The scoreboard artifact, (i.e., the `rsv_socreboard` class, not shown), which collects coverage data in simulation. It does not have a corresponding module-based part.

![http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_rsv_rtl.jpg](http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_rsv_rtl.jpg)

## `ReSim` built-in Artifacts (Class-based Artifacts) ##

### CP Class ###

The CP class, i.e., the rsv\_configuration\_port class, controls the operations of the CP wrapper. ReSim provides a simplified model of the Internal Configuration Access Port (ICAP). It is implemented by the `rsv_icap_virtex` class and the `rsv_rsv_sbt_parser` class.

  * Support partial reconfiguration and configuration readback (including readback busy)
  * Support 32-bit mode
  * Support ICAP registers: CRC, CMD, FAR, FDRI, FDRO, IDCODE.
  * Support ICAP commands: NULL, WCFG, RCFG, RCRC, GRESTORE, GCAPTURE, DESYNC.

### RR Class ###

The RR class, i.e., the `rsv_region` class, controls the operations of the RR wrapper, and is composed of a `rsv_portal_controller`, a `rsv_error_injector`, and a `rsv_state_spy` class.

  * Portal Controller (i.e., the `rsv_portal_controller` class): Controls module swapping by selecting a MUX-like `module_selector`, which connects one and only one active RM to the static region.

  * Error Injector (i.e., the `rsv_error_injector` class): Inject errors to the static region so as to mimic the spurious RM outputs during reconfiguration; Inject errors to the RMs so as to mimic the undefined initial RM state after reconfiguration.

  * State Spy (i.e., the `rsv_state_spy` class): Synchronize state data of the simulated RMs with the contents of the `spy_memory` module, which mimics the configuration memory of the target FPGA.

### Simulation-only Layer Class ###

The simulation-only layer artifact is the container for ReSim built-in artifacts. It is the root of class-based artifacts. It instantiates the CP class and the RR classes, as well as a scoreboard artifact.

### Scoreboad Class ###

The scoreboard artifact, (i.e., the `rsv_socreboard` class), collects coverage data in simulation. The default scoreboard collects the coverage of the RRID/RMID fields of SimBs. In particular,

  * It collects whether all RMs have been exercised (i.e., to cover all RMs)

  * It collects whether each RM has been reconfigured to every other RM (i.e., to cover all possible transitions between RMs)


## `ReSim`-generated Artifacts (Module-based Artifacts) ##

### CP Wrapper ###

The CP wrapper is instantiated in the user design hierarchy as the configuration port. It has the same IO signals as the real configuration port.

  * For simulation (using ReSim): The simulation version of the CP wrapper groups IO signals of the configuration port into an `icap_if`.

  * For implementation (using e.g., PlanAhead [xilinx\_ug702\_partial](xilinx_ug702_partial.md)): The implementation version of the CP wrapper instantiates the ICAP primitive from Xilinx.

### RR Wrapper ###

The RR wrapper for each RR is used as a placeholder for the RR to which RMs are mapped. ReSim automatically generates the source code for the RR wrapper.

  * For simulation (using ReSim): The simulation version instantiates both RMs as well as other simulation-only artifacts.

  * For implementation (using e.g., PlanAhead [xilinx\_ug702\_partial](xilinx_ug702_partial.md)): Since the static region and the RMs are implemented separately, ReSim generates one version for synthesizing static region and one for each RM. The RR wrapper for synthesizing the static design is a black box whereas the RR wrapper for synthesizing each RM directly wraps the RM.

#### Module Selector ####

The `module_selector` module selects one active module according to the currently active RMID.


#### Phase Selector ####

The `phase_selector` module connects/disconnects the error sources to/from the currently active module and the static region according to whether or not the configuration data section of a SimB is being written to the CP artifact.

#### Spy Memory ####

The `spy_memory` module models the configuration memory of the simulation-only layer. The following figure compares the configuration memory of Virtex-5 FPGA, as an example of real FPGA devices, with the `spy_memory` of ReSim. Looking at the FPGA floorplan (left half of the figure), the user design are represented by resource blocks such as Configurable Logic Blocks (CLB) and Block RAMs (BRAM), and are mapped to configuration bits in the configuration memory. Each bit of the configuration memory either represents the logic settings (i.e., the logic function and the connection) or the execution state (i.e., filp-flop values, BRAM content) of the user design. Using CLB as example, an array of 20 x 1 CLBs are indexed in the configuration memory by a configuration Row Address (RA) and Column Address (CA). The array is mapped to 36 configuration frames, each of which is further indexed by a Minor Address (MNA). One frame contains 41 32-bit words and one each bit is indexed by the Bit Offset (BO) within the frame. Thus, in order to locate one configuration bit, the designer needs to know the RA, CA, MNA and BO.

![http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_gc_c2s.jpg](http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_gc_c2s.jpg)

In ReSim-based simulation, the FPGA fabric is substituted with the simulation-only layer, whose configuration memory is illustrated in the right half of the figure. In the simulation-only layer, each RR and RM is given a numerical ID (RRID & RMID). The example shown in Figure has 3 RRs with RRID = 0,1,2 and RR0, for example, has 2 RMs with RMID = 0,1. Note that the RMIDs commence at 0 for each RR. Each RR is composed of N frames where N is a user-defined parameter specified in the Tcl script (see the `rsv_create_region` API). A simulation-only frame is indexed by a minor address (MNA) and contains 4 words, where word 0 stores a 32-bit signature of the RM and words 1-3 stores execution state (i.e., RTL signal values) of the RM.

On real FPGAs, the state of a multi-bit register is flattened into individual flip-flops that are mapped to the configuration memory bit by bit. However in ReSim, a multi-bit register (typically represented by RTL signals in the HDL code) is stored contiguously. This improves the debugging productivity because at RTL level, signals are typically grouped. Thus in order to locate one user design signal in the configuration memory, the designer needs to know the RRID, RMID, MNA, Bit Offset (BO) and the Bit Width (BW) of the signal.

### Simulation-only Layer Wrapper ###

The simulation-only layer wrapper starts the simulation-only artifacts. It is a module without any input or output, and is typically placed in the testbench.

### Simulation-only Bitstream ###

As simulation cannot effectively make use of a real bitstream, the simulation-only layer substitutes a simulation-only bitstream (SimB) to model the bitstream traffic. The SimB captures the essence of a real bitstream but its size is significantly reduced.

The following table illustrate an example of SimB for reconfiguring a module. In general, a SimB captures the essence of a real bitstream and only keeps sections that are relevant to simulation. In the table, the bold sections indicate sections that are different from real bitstreams.

| 0xAA995566 | SYNC Word                             |
|:-----------|:--------------------------------------|
| 0x20000000 | Type 1 Nop                            |
| 0x30000001 | Type 1 Wr CRC                         |
| 0xBACF3AB6 | **Signature**                           |
| 0x30002001 | Type 1 Wr FAR                         |
| 0x00010000 | **RRid:0x00, RMid:0x01, MNA:0x0000**    |
| 0x30008001 | Type 1 Wr CMD                         |
| 0x00000001 | WCFG                                  |
| 0x30004000 | Type 1 Wr FDRI                        |
| 0x50000008 | Type 2 Wr 8 Words                     |
| 0x97B376FA | **Configuration data: Frame 0, Word 0** |
| 0x00000000 | **Configuration data: Frame 0, Word 1** |
| 0x00000000 | **Configuration data: Frame 0, Word 2** |
| 0x00000000 | **Configuration data: Frame 0, Word 3** |
| 0x2D7C4CAC | **Configuration data: Frame 1, Word 0** |
| 0x00000000 | **Configuration data: Frame 1, Word 1** |
| 0x00000000 | **Configuration data: Frame 1, Word 2** |
| 0x00000000 | **Configuration data: Frame 1, Word 3** |
| 0x20000000 | Type 1 Nop                            |
| 0x20000000 | Type 1 Nop                            |
| 0x30008001 | Type 1 Wr CMD                         |
| 0x0000000D | DESYNC                                |
| 0x20000000 | Type 1 Nop                            |
| 0x20000000 | Type 1 Nop                            |

  * **Signature:** A signature is the XORed value of Word 0 of each configuration frame of an RM. In this example, `0xBACF3AB6 = 0x97B376FA XOR 0x2D7C4CAC`

  * **FAR:** The frame address is the aggregation of the RRID, RMID and MNA of the target RM to be swapped in. MNA is typically 0x0000 indicating that partial reconfiguration starts from the very 1st frame.

  * **Configuration data:** The configuration data is to be written to the `spy_memory`. This example has 2 frames and each frame has 4 words.

### Simulation-only Logic Allocation Files (`.sll` files) ###

Vendor tools generate a logic allocation file (`.ll` file) indicating the mapping of user-defined flip-flops to the bits in the configuration memory. The figure shows an example of an entry in the `.ll` file. The `rm_statistic[0]` flip-flop is allocated to Frame Address (FA) `0x0001851f`, from which the designer can decompose the RA, CA and MNA (see the bit composition of the frame address in the figure). The example also indicates that the flip-flop is mapped to the 259th bit of the frame (indexing from 0).

To map RTL signals to the configuration memory, ReSim treats the simulation-only logic allocation file (`.sll` file) as being equivalent to the logic allocation file generated by the FPGA vendor tools. The figure provides an example of the `.sll` file. The statistic register is located at Frame Address `0x00010002`, which is decomposed into RRID = 0, RMID = 1 and MNA = 2. The BO and BW fields indicate that the statistic register starts at bit 36 and is 32 bits wide.

It should be noted that ReSim only generate a template `.sll` file and by default, no signal is mapped to the configuration memory. It is up to the designer to decide whether it is necessary to map RTL signal to the configuration memory and which frame address should an RTL signal be mapped to. Typically, the `.sll` file is only used to test designs that saves and restores module state via the configuration port (see the [FPGA2012](http://resim-simulating-partial-reconfiguration.googlecode.com/files/state.short.proceedings.p241-gong.pdf) paper)

### SystemVerilog Package ###

The ReSim-generated SystemVerilog package file includes ReSim-generated artifacts in a single file. It is used for compilation purposes.

### SystemVerilog Interfaces ###

The parameter script defines the interfacing signals that cross the RR boundary. This list of signals are grouped in the a SystemVerilog interface and its source code is generated by ReSim.

### TODO-LIST File ###

The TODO-LIST file describes the steps involved to start a ReSim-based simulation run. In particular, it contains ModelSim scripts to compile the ReSim library and to run the simulation.

### Report File ###

The report file includes the assignment of IDs to RMs and RRs in the user design.

### Derived Class ###

The default behavior of the generated artifacts and the built-in artifacts can be modified for design-/test-specific needs. The following are typically usage examples of deriving and overriding the default class implementation.

#### Device-specific reconfiguration interface. ####

The default  class models the Virtex-4,5 and 6 FPGA families, which operate on 32-bit SimBs and produce one rsv\_simb\_trans transaction every cycle. The rsv\_icap\_virtex class can be derived to support new FPGA families. For example,

  * For DRS designs targeting Spartan-6 devices, the designer can derive an rsv\_icap\_spartan class that operates on a half SimB word (16-bits).

  * For DRS designs targeting Altera FPGAs, the designer can derive an rsv\_cp\_stratix class that implements the reconfiguration interfacing protocol of Altera devices.

#### Generic SimB Parser. ####

The default  class is a generic SimB parser that are independent of the FPGA family and interpret simulation-only bitstreams. The rsv\_sbt\_parser class can be derived and extended to

  * Parse and interpret real bitstreams

#### Error Injector. ####

By default, the  class drives undefined “x” values as error sources. The designer can derive the error injector to define design-/test-specific error sources, such as,

  * Stuck-at-zero errors
  * Stuck-at-one errors
  * Random signal values
  * Glitches
  * Design-/test-specific error sequence, such as, spurious interrupt requests, spurious bus master transaction requests, spurious data packets to the RM, ...

#### Scoreboard. ####

The default  class collects the coverage of the RRID/RMID fields of SimBs. The designers can add design-/test-specific coverage items to a derived scoreboard class. For example

  * For designs that have multiple RRs, simulation needs to collect cross-coverage of the combination of RMs mapped to multiple RRs


## Tcl APIs ##

### rsv\_cleanup ###

  * **Usage:** `rsv_cleanup`
  * **Description:** Clean up all ReSim related global variables in the Tcl interpreter. It is typically used at the beginning or the end of the parameter description script.

### rsv\_create\_portmap ###

  * **Usage:** `rsv_create_portmap portmap_name clock_name`
  * **Description:** Define a portmap named `portmap_name` with a clock named `clock_name`. In ReSim, a portmap groups the IO signals of a reconfigurable region (RR). The portmap is used by all reconfigurable modules (RM). The concept is similar to _SystemVerilog Interface_. ReSim only supports RRs with one and only one clock.
  * **Examples:**

```
rsv_create_portmap "rr_if" "clk" // Create a portmap "rr_if" which has a clock signal "clk"
```

### rsv\_add\_port ###

  * **Usage:** `rsv_add_port portmap_name signal_name signal_direction optional_signal_width`
  * **Description:** Add IO signal named `signal_name` to the portmap named `portmap_name`. A portmap must already been defined by `rsv_create_portmap`. Parameter `signal_direction` is either "in" or "out" and parameter `optional_signal_width` is optional and is 1 by default.
  * **Examples:**

```
rsv_add_port "rr_if" "rstn" in // Add the "rstn" input to the "rr_if"
rsv_add_port "rr_if" "data" out 32 // Add the 32-bit "data" output to the "rr_if"
```

### rsv\_create\_region ###

  * **Usage:** `rsv_create_region region_name portmap_name region_size reserved_argument optional_error_injector_name`
  * **Description:** Define a reconfigurable region (RR) named `region_name` which uses the `portmap_name` portmap. The RR contains `region_size` number of frames (NOTE, each frame contains 4 words in ReSim), which determines the size of the generated SimB. Each region can have an optional error injector.
  * **Examples:**

```
rsv_create_region "my_rr" "rr_if" 8 "" "" // Create an RR that use "rr_if" as the portmap and has 8 frames.
rsv_create_region "my_rr" "rr_if" 8 "" "my_ei" // Also attach a "my_ei" error_injector to the RR.

```

  * **Note1:** In ReSim-based simulation, an error injector mimics the spurious RM outputs and undefined RM state during reconfiguration. In most cases, the automatically generated error injector is already enough for simulation. You can edit the generated source code for advanced usage. If you do not wish to use the error injector, please do not specify the parameter. Please see the released examples for using the error injector.
  * **Note2:** `region_name` is the design unit name and user can specify arbitrary instance name.
  * **Note3:** In ReSim-based simulation, RRs must have unique names. Even if a design has two same RR (same IOs, same RMs etc ...), they must be created separately by two `rsv_create_region` calls with two different names.
  * **Note4:** Users must instantiate the RR named `module_name` in higher level of the design hierarchy.
  * **Note5:** The argument `reserved_argument` is reserved and the user should pass a null string `""` to the argument. This argument was used to specify a monitor of the reconfigurable region in previous versions of ReSim.

### rsv\_add\_module ###

  * **Usage:** `rsv_add_module region_name module_name optional_module_parameter_list`
  * **Description:** Add a reconfigurable module (RM) named `module_name` to the reconfigurable region (RR) named `region_name`. As an option, you can pass Verilog parameter/VHDL generic values to the module.
  * **Examples:**

```
rsv_add_module "my_rr" "module_a" "" // Add the module "module_a" to the region "my_rr". 
rsv_add_module "my_rr" "module_a" "#(24,3)" // Non-default parameter value. 
rsv_add_module "my_rr" "module_a" "#(.p1(3),.p0(24))" // Non-default parameter value using name association.
rsv_add_module "my_rr" "module_a" "#(.p1(5))" // Override the default value of parameter p1 to 5
```

  * **Note1:** The parameter list are passed as a Tcl string and are used directly to instantiate the module. Within the Tcl string, the parameter list uses Verilog Syntax.
  * **Note2:** `module_name` is the design unit name and the instance name is always "rm0, rm1 .... ".
  * **Note3:** In ReSim-based simulation, Each RR can have multiple copies of a same RM. The RM can have same or different parameter list values. However, they must be added separately by two `rsv_add_module` calls with a same different `module_name`.
  * **Note4:** Users must define and compile the RM named `module_name`.

### rsv\_create\_solyr ###

  * **Usage:** `rsv_create_solyr simulation_only_layer_name targe_fpga_family optional_scoreboard_name`
  * **Description:** Define the simulation-only layer named `simulation_only_layer_name` which targets the specified FPGA family. The parameter `targe_fpga_family` can be "VIRTEX4", "VIRTEX5", "VIRTEX6". Each simulation-only layer can have an optional scoreboard.
  * **Examples:**

```
rsv_create_solyr "my_sim_only_layer" "VIRTEX5" "" // Create the simulation-only later targeting VIRTEX5.
rsv_create_solyr "my_sim_only_layer" "VIRTEX5" "my_scb" // Also attach a "my_scb" scoreboard.

```

  * **Note1:** In ReSim-based simulation, a scoreboard collects collects coverage data. In most cases, users do not have to create a scoreboard. The default scoreboard collects coverage data for transitions between RMs (e.g., Whether all RMs in an RR have been exercised?).

### rsv\_add\_region ###

  * **Usage:** `rsv_add_region solyr_name region_name`
  * **Description:** Add the reconfigurable region `region_name` to the simulation-only layer `solyr_name`.
  * **Examples:**

```
rsv_add_region "my_sim_only_layer" "my_rr" // Add the region "my_rr" to the simulation-only layer. 
```

### rsv\_gen\_solyr ###

  * **Usage:** `rsv_gen_solyr solyr_name`
  * **Description:** Generate source code for the simulation-only layer `solyr_name`, and the simulation-only bitstream to be used as test stimuli. It also generate a TO\_DO\_LIST file that explains the steps to instantiate and use the generated code.
  * **Examples:**

```
rsv_gen_solyr "my_sim_only_layer" // Generate the source coed for the simulation-only layer
```

### rsv\_create\_memory ###

  * **Usage:** `rsv_create_memory memory_name granularity number_of_banks endian`
  * **Description:** The generated SimB are in binary format (See ./artifacts/sbt/xxxx.sbt) and can not be used by simulation directly. The `rsv_create_memory` and the `rsv_add_2_memory` APIs convert the binary SBT into a "memory format" that are ready to be loaded into ModelSim. This API defines the format of the memory named `memory_name`. The parameter `granularity` indicates the smallest addressable unit in bytes of the memory. Granularity=4 means 4-byte addressable or word-addressable. The parameter `number_of_banks` specifies the number of memory banks that are connected in parallel. The parameter `endian` can be either "le" for little endian or "be" for big endian. The converted SBT files can be found at `./artifacts/sbt/memory_name_bank0,1,2...txt`
  * **Examples:**

```
rsv_create_memory "zbt" 4 1 be // zbt: 4-byte-addressed, 1 bank, big endian
rsv_create_memory "ddr2" 2 4 le // ddr2: 2-byte-addressed, 4 banks, little endian
```

  * **Note1:** Users can also create in-house tools to parse/use/convert SimBs.

### rsv\_add\_2\_memory ###

  * **Usage:** `rsv_add_2_memory memory_name simb_file_name memory_address`
  * **Description:** Convert the binary SimB file `simb_file_name` to memory format loadable by ModelSim. The SimB is expected to be loaded to address `memory_address` of the memory. The parameter `memory_address` is calculated in turns of the granularity specified in `rsv_create_memory`. Fox example, the address 0x100 indicates the 0x100th entry of the memory. If the memory granularity is 4, the byte address of SimB is therefore 0x400.
  * **Examples:**

```
rsv_add_2_memory "zbt" "./artifacts/sbt/my_rr_rm0.sbt" 0x100 // Add generated SimB to memory starting from 0x100
rsv_add_2_memory "zbt" "./my.sbt" 0x100 // Add user specified SimB to memory starting from 0x100
```

  * **Note1:** Users can also create in-house tools to parse/use/convert SimBs.

### rsv\_gen\_sbt ###

  * **Usage:** `rsv_gen_sbt simb_file_name simb_op simb_fa simb_wc`
  * **Description:** Generate the binary SimB file `simb_file_name`. The parameter `simb_op` can be either "WCFG" for reconfiguration or "RCFG" for configuration readback. The parameter `simb_fa` is the frame address of the generated SimB. The parameter `simb_wc` specifies the size of the configuration data section (i.e., 4x `region_size`).
  * **Return:** The calculated signature of the SimB.
  * **Examples:**

```
rsv_gen_sbt "./my" WCFG 0x01020000 32 // Generate a SimB for partial reconfiguration (RRid=0x01,RMid=0x02)
rsv_gen_sbt "./my" RCFG 0x01020001 4 // Generate a readback SimB  for one frame (RRid=0x01,RMid=0x02,MNA=0x0001)
```

  * **Note1:** This API is typically automatically called by ReSim. However, advanced users may wish to use it to generate and customize SimB.
  * **Note2:** Do not include the .sbt extension to the SimB file name `simb_file_name`. The extension is automatically pended by ReSim.

### rsv\_parse\_sbt ###

  * **Usage:** `rsv_parse_sbt simb_file_name`
  * **Description:** Parse the binary SimB file `simb_file_name` and dump the results to a text file named `simb_file_name.txt`.
  * **Examples:**

```
rsv_parse_sbt "./my" // Parse and dump a SimB ./my.sbt
```

  * **Note1:** This API is typically automatically called by ReSim. However, advanced users may wish to use it to generate and customize SimB.
  * **Note2:** Do not include the .sbt extension to the SimB file name `simb_file_name`. The extension is automatically pended by ReSim.

### rsv\_iei\_hdl\_state ###

  * **Usage:** `rsv_iei_hdl_state rr_inst rm_inst iei_sig_type iei_mem_type`}
  * **Description:** Inject errors to all internal signals of module `rm_inst` in reconfigurable region `rr_inst`. This API injects errors to both signals and memory cells of the RTL design. The type of error can be "none", "zero" OR. "x" for signals, and "none", "zero" OR. "rand" for memory cells.
  * **Examples:**

```
rsv_iei_hdl_state "/tb/dut/rr0" "rm0" "x" "rand"// Inject X and random value to design object /tb/dut/rr0/rm0 
rsv_iei_hdl_state "/tb/dut/rr1" "rm2" "x" "none"// Inject X to signals of design object /tb/dut/rr1/rm2 
```

  * **Note1:** This API is typically called in the error injector during reconfiguration. It can also be used in other places to inject errors.
  * **Note2:** Limited by the implementation of ReSim, this task can only inject errors to Verilog registers (i.e., NOT Verilog nets or VHDL signals).
  * **Note3:** User can use the ```rsv_execute_tcl`` macro to call such Tcl API (and other Tcl APIs) from SystemVerilog test code.