# Frequently Asked Questions #

This wiki page contains frequently asked questions by users and reviewers of the `ReSim` library. For an overview of the `ReSim` library, please refer to the [ReSim Overview](ReSim.md) page.



### Q. Why do I have to simulate the reconfiguration process? Isn't it enough to simulate each configuration of the design? ###

FPGA vendors such as Xilinx claim that the various configurations of a DRS can be individually simulated and tested, but do not support simulating the reconfiguration process itself `[`[UG702](http://www.xilinx.com/support/documentation/sw_manuals/xilinx12_4/ug702.pdf)`]`. However, correctly verified sub-systems, while necessary, are not sufficient since the most costly bugs are encountered in system integration `[`[ITRS\_2009](http://www.itrs.net/home.html)`]`. For the sake of system-level verification, it is essential to simulate the reconfiguration process as part of an _integrated_ simulation and debugging environment.

<a href='Hidden comment: 
Case Study: AutoVision bugs ... -> Integration bugs
'></a>

### Q. What could potentially go wrong in the reconfiguration process? ###

In general, each part of the reconfiguration machinery (i.e., the logic that performs the _synchronization_, _isolation_, _initialization_ of RMs and the _bitstream transfer_) could have design bugs. For a specific DRS design, it relay depends on the nature of the design itself and the experience of the designer as to where the bugs could come from. Interested users can refer to the bugs in various case studies in the [published papers](Published_Papers.md)

### Q. What `ReSim` is aiming to verify? Is `ReSim` verifying the functionality of the FPGA fabric? ###

Since ReSim mimics the behavior of the FPGA fabric (see the [ReSim Overview](ReSim.md) page), one common confusion would be to think of ReSim-based simulation as verifying the FPGA fabric (the ICAP, configuration memory, etc).

The FPGA fabric is expected to be thoroughly verified by vendors. On the other hand, ReSim models the FPGA fabric for the sake of testing the user design. In simulation, the user logic (modeled by VHDL/Verilog) interacts with the simulation-only artifacts (e.g., the ICAP artifact) as if it is running on a real FPGA. This is similar to the concept of a _Bus Function Model_ (BFM), which mimics the behavior of bus masters to test peripheral logic attached to the bus.


### Q. What are other approaches to simulate partial reconfiguration? What's the main difference between `ReSim` and other approaches? ###

The classic approach of simulating partial reconfiguration is to use a MUX to select one and only one reconfigurable module from all possible modules. MUX-based approaches assume the reconfiguration delay is either zero or a constant number.

Although ReSim also use MUX to connect reconfigurable modules in parallel (see the [ReSim Overview](ReSim.md) page), the selection of the MUX is controlled by writing a SimB to the simulated ICAP artifact. In particular, ReSim supports the simulation of bitstream transfer and the effect of module swapping as if the user design is running on target FPGAs. Therefore, in ReSim-based simulation,

  * The logic that transfer the bitstream (i.e., the bitstream datapath) is simulated and tested.
  * The simulated reconfiguration events is as releastic as the implemented design. For example, the module swapping could be delayed by an unexpected interrupt in the bistream transfer operation. A module is not swapped in untill all bytes of the SimB is successfully written to the ICAP.

Please refer to the [published papers](Published_Papers.md) for more details on the novelty of using ReSim.

### Q. Could `ReSim`-based simulation detect all the bugs related to the reconfiguration machinery of a DRS design? ###

First of all, design errors are typically categorized into functional bugs (e.g., cycle-mismatch in the reconfiguration machinery) and physical/implementation bugs (e.g., potential short circuit in the reconfiguration process, wiring/routing problems in the reconfigurable region). ReSim is used for RTL simulation and thereby assists in detecting functional bugs. If a designer uses standard partial reconfiguration tool flow offered by vendors (e.g., the PlanAhead software), vendor tools would usually focus on physical bugs.

In terms of functional bugs, ReSim-based simulation assists in detecting bugs but does not guarantee a bug-free design. Similar to the functional verification of static designs, there is no magic tool that automatically verifies everything. For a bug to be detected by a designer,

(1) selected test stimuli needs to be driven to the design to expose the buggy scenario
(2) the bug needs propagate to the observation points of the testbench
(3) the simulation must accurately simulates the design behavior

The designer needs to put their efforts on (1) and (2) whereas ReSim aims to achieve (3).

### Q. How accurate is `ReSim`-based simulation compared with the behavior of the implemented design on a target FPGA? ###

Following the previous question, the simulation accuracy is an important factor for functional verification. Unfortunately, ReSim-based simulation does not promise 100% simulation accuracy. However, full simulation accuracy requires simulating the entire FPGA fabric, which calls for too many details and overheads (see the [ReSim Overview](ReSim.md) page). For the sake of verification productivity, it is essential to find the right balance between the accuracy of simulation and the details of the fabric being modeled.

As ReSim abstracts out the details of the FPGA fabric, the simulation-only layer can be regarded as a _vendor-independent_ device. Simulation can be thought of as functionally verifying a design on such a vendor-independent device. Although RTL simulation is only an approximation to the target device, our case studies demonstrated that with negligible development and simulation overhead, simulation using ReSim captured a reasonable number of bugs and avoided most of the costly iterations of using Chipscope.

### Q. If `ReSim`-based simulation is not accurate, why not just program the FPGA directly and debug using `ChipScope`? ###

In traditional static designs, RTL simulation also could not replace on-chip debugging using ChipScope. In particular, simulation is typically used in the early stage of a design project and ChipScope is used when the design is mature enough to run a long time without frequent failures.

For DPR designs, ReSim does not aim to replace on-chip debugging using ChipScope. Rather, ReSim assists in detecting most of design bugs so as to reduce, if not avoid, the costly iteration of on-chip debugging.

Ultimately, it is up to the designer to understand the pros and cons of various tools available and to utilize the tools in their verification flow. For the case studies we have performed, the overhead of integrating ReSim into the existing simulation and verification flow is trivial, whereas the benefit is, potentially, being able to detect _most_ DPR-related bugs before on-chip debugging.

### Q. What FPGA architectures does `ReSim` support? ###

As ReSim abstracts out the details of the FPGA fabric, in theory, ReSim is able to simulate designs on all FPGA architectures. However, the implementation of ReSim does use some architecture specific information (e.g. the timing of the ICAP port). Up till now, ReSim has been tested
on DPR designs that run on Virtex 4,5,6.

ReSim is designed for reusability and flexibility. In particular, ReSim is implemented using Object Oriented Programming techniques and a new FPGA architecture can be added by extending the original class library. The [FPT2012 paper](http://resim-simulating-partial-reconfiguration.googlecode.com/files/resim.proceedings.pdf) discussed the reusability of the library. If you really wish to use ReSim one other architectures, you can also contact the authors for help.

### Q. In the implementation of `ReSim`, do the developers use any "internal" information from the FPGA vendors? ###

No, ReSim only utilizes information in public documentation released by vendors.