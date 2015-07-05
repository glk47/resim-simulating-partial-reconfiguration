# ReSim and ReSim-based Simulation #

**ReSim** is a reusable, open source simulation library to support _cycle-accurate_ [Register Transfer Level (RTL)](http://en.wikipedia.org/wiki/Register-transfer_level) [logic simulation](http://en.wikipedia.org/wiki/Logic_simulation) of DRS designs (i.e., FPGA designs capable of [partial reconfiguration](http://en.wikipedia.org/wiki/Partial_re-configuration). It assists designers in verifying integrated DRS designs BEFORE, DURING and AFTER partial reconfiguration, including the transfer of configuration bitstreams and the subsequent module swapping.

## Motivation ##

Compared with traditional static FPGA designs, DPR has introduced additional flexibility for system designers but has also introduced challenges to the verification of design functionality. FPGA vendors such as Xilinx claim that each valid configuration of a DRS can be individually tested using traditional simulation methods, but do not support simulating the reconfiguration process itself. However, partial reconfiguration should not be viewed as an isolated process. Although correctly verified sub-systems are necessary, they are not sufficient for ensuring design correctness since the most costly bugs are encountered in system integration. Although Altera proposed to support behavioral simulation of the reconfiguration process, it has not yet incorporated such simulation support into its tool flow. As a result, new simulation approaches need to extend traditional simulation techniques to assist designers in testing and debugging DRS designs while part of the design is undergoing reconfiguration.

## Background of Partial Reconfiguration ##

An FPGA-based hardware design has two layers: the user-design layer and the physical layer. The user-design layer is, more or less, your RTL code. It describes the desired logic function of your design. The physical layer is the actual FPGA fabric (e.g., LUTs, FFs, routing switches) that your RTL code is mapped to.

For a typical DRS design, multiple hardware Reconfigurable Modules (RMs) are mapped to the same Reconfigurable Region (RR) and communicate with the static circuitry to perform the required tasks. BEFORE reconfiguration, the static logic should properly _synchronize_ with the old RM to pause the ongoing computation. DURING reconfiguration, a reconfiguration controller _transfers_ the configuration bitstream of the new RM to the configuration port (e.g., Internal Configuration Access Port, ICAP) and then to the configuration memory of the FPGA fabric. The bitstream contains the configuration information about the FPGA fabric so that the logic and the routing of the RM is changed. A new RM is swapped in upon the completion of bitstream transfer. During this period, the static part must _isolate_ the RR to avoid the propagation of spurious outputs from partially configured RMs. AFTER reconfiguration, the incoming RM needs to be _initialized_ to a known state before it starts execution.

![http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_solyr_3l.jpg](http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_solyr_3l.jpg)

We highlight two points from the above description:

  * From a user-design perspective, partial reconfiguration is the process of _synchronizing_, _isolating_, _initializing_ RMs and _transferring bitstreams_. We refer to the user-design modules that do all these as the reconfiguration machinery (moderately shaded blocks in the figure).

  * From a physical layer perspective, partial reconfiguration is the process of a new configuration bitstream updating the old configuration information of the FPGA fabric thereby changing the functionality of the design.


## Challenges of Simulating DRS designs ##

A not very scientific way of defining functional verification is that functional verification is to "simulate and debug your RTL code". For the functional verification of DRS designs, our primary focus is to "simulate and debug the RTL code for the reconfiguration machinery". As we found in our [ReSim Case Studies(PDF)](http://code.google.com/p/resim-simulating-partial-reconfiguration/downloads/detail?name=resim_doc_casestudies_v2_3b.pdf&can=2&q=), the reconfiguration machinery is prone to design error.

One significant challenge of simulating partial reconfiguration is that accurate and simulation of the process requires the RTL code of the FPGA fabric, in additional to the RTL code of your design. Normally, a designer will not be able to get the RTL code of the target FPGA device. Therefore, Conventional RTL simulation methods can not be used to verify a DRS design. On the other hand, even if a design has access to the RTL code of the FPGA fabric, simulating the FPGA device with your own RTL code would include a multitude of unnecessary details for verification and would significantly reduce verification productivity. The designer wishes to focus on verifying the user logic and, for the sake of efficiency, requires the simulation to abstract away the details of the FPGA fabric. Therefore,

> An ideal simulation method needs to find the right _balance_ between the _accuracy of simulation_ and _the details of the fabric being modeled_.

## The core idea of ReSim and ReSim-based simulation ##

From the designer's perspective, ReSim can be viewed as a Verification IP that mimics the target FPGA to which the user design is mapped. The following figure redraws the conceptual diagram of typical DRS designs with all the physically dependent blocks (solid black boxes) replaced by their corresponding simulation-only artifacts (open black boxes). In particular, the configuration bitstreams are replaced by simulation-only bitstreams (SimB), possible configuration ports are represented by a CP artifact, and the part of configuration memory to which each RR is mapped is substituted by an RR artifact.

![http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_solyr_3lsim.jpg](http://resim-simulating-partial-reconfiguration.googlecode.com/files/fig_solyr_3lsim.jpg)

Using a simulation-only layer, reconfiguration is simulated as follows: the user-defined reconfiguration controller transfers a SimB instead of a real bitstream to the CP artifact. While the SimB is being written, the RR artifact injects errors to both the static region and the RM. Errors injected to the static region model the spurious outputs of the module undergoing reconfiguration and help to test the isolation logic of the user design. Errors injected to the reconfigurable modules model the undefined initial state of the RM and help to test the initialization mechanism of the design. After the SimB has been completely written to the CP artifact, the RR artifact checks the signature of the SimB, extracts the numerical ID of the new RM, and drives module swapping according to the extracted ID. Using the simulation-only layer, we can simulate more complex reconfiguration activities such as saving/restoring module state, fine grained reconfiguration, module relocation. Please check our [ReSim User Guide(PDF)](http://code.google.com/p/resim-simulating-partial-reconfiguration/downloads/detail?name=resim_doc_gettingstarted_v2_3b.pdf&can=2&q=).

In simulation, the SimB mimics the impact of real bitstreams on the simulated user design. Instead of containing bit-level configuration memory settings for the module to be configured, as found in a real bitstream, a SimB contains numerical IDs for the module to be configured and the target reconfigurable region. In addition, the length of a SimB is significantly shorter than a real bitstream and can be adjusted to test various scenarios of the bitstream transfer mechanism (e.g., FIFO overflow/underflow).

Use of a simulation-only layer to emulate an FPGA device is analogous to the
use of a Bus Functional Model (BFM) to emulate a microprocessor when testing
and verifying peripheral logic attached to a microprocessor bus. Although
the BFM is not a completely accurate representation of the microprocessor, it is
accurate enough to capture the interactions between the microprocessor and the
bus peripheral to be tested. Furthermore, since the BFM approach abstracts away
the internal behaviors of a processor such as pipelines, BFM-based simulation is
more productive than simulating a completely accurate processor model. Similarly,
the simulation-only layer emulates the FPGA device and captures the interactions
between the physical device and the user design to be tested. Furthermore, the
simulation-only layer abstracts away the details of the FPGA fabric and significantly improves the verification productivity compared with fabric-accurate simulation.

## Capabilities and Limitations ##

ReSim-based simulation can be viewed as testing the DRS design on _fabric-independent FPGA architecture_. It captures the essential features of DRS designs. Therefore, ReSim aims to _assist_ designers in detecting _functional bugs_ of DRS designs. For example,

  * System deadlock due to the inavaliability of module undergoing reconfiguration
  * Software bugs in controlling partial reconfiguration, such as, setting an incorrect bitstream transfer size, passing an invalid bitstream storage buffer pointer, memory/cache coherence problem of bitstream storage buffers ...
  * Bugs in synchronizing the static region and RMs before reconfiguration, such as, failing to block a reconfiguration request until the RM is idle ...
  * Bugs in the bitstream transfer logic, such as, cycle mismatches, FIFO overflow, errors in driving the ICAP signals ...
  * Bugs in isolating the region undergoing reconfiguration, such as, isolating the RR too early or too late, ..., and
  * Bugs in initializing the newly configured module, such as, resetting the RM before it is completely reconfigured, loading the RM pipelines with incorrect data.

Since ReSim abstracts away the physical details of the target device, it could offer limited help to bugs that are related to the FPGA fabric, i.e., fabric-dependent bugs, such as

  * Errors in the bitstream itself (e.g., setting an incorrect Frame Address in the bitstream, single or multiple bit flips in the bitstream), and
  * Errors in interpreting the content of the bitstream (e.g. accessing an incorrect state bit in a bitstream).

Furthermore, ReSim does not and does not aim to provide assistance in verifying implementation-related bugs, such as:

  * Timing violation errors in the placed and routed design, and
  * Possible short or open circuits, if any, caused by partial reconfiguration

In general, if the designer use standard PR tool flow offerred by the vendor, these bugs could, _in theory_, be avoided. On the other hand, if the system is designed to directly manipulate the generated bitstreams or even assembly bitstreams on-the-fly, ReSim could only offer limited help to test and verify it.

Meanwhile, limited by the complexity of implementing ReSim, ReSim only supports,

  * ModelSim 6.5g (thoroughly tested) or above (in theory)
  * Virtex 4,5,6 FPGAs
  * The basic operations of ICAP: 32-bit ICAP, configuration write, configuration readback (including readback busy), basic configuration registers(i.e., CRC, CMD, FAR, FDRI, FDRO, IDCODE) and basic commands (NULL, WCFG, RCFG, RCRC, GRESTORE, GCAPTURE, DESYNC)
  * For VHDL designs, errors can only be injected to RMs via their IO signals. For Verilog designs, errors can be injected to internal signals of RMs directly.
  * Saving and restoring flip-flop/register values via the configuration port.
  * State restoration by modifying the state bit (i.e. INT0/INT1 bit) of a bitstream.

ReSim does not yet support,

  * Other HDL simulators (because ReSim uses ModelSim built-in commands)
  * Xilinx 7 series FPGAs or Altera FPGAs
  * Advanced operations of ICAP: abort sequence, status register readback, etc
  * Saving and restoring BRAM values via the configuration port.
  * State restoration by modifying the SET/RESET bit of a bitstream.