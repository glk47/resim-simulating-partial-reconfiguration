# ReSim: RTL Simulation of Dynamic Partial Reconfiguration and its FPGA Systems #

[Dr. Lingkan (George) Gong](Lingkan_Gong.md)<sup>1</sup>, [Dr. Oliver Diessel](http://www.cse.unsw.edu.au/~odiessel/)<sup>2</sup>

Reconfigurable Systems Group, The University of New South Wales, Sydney, Australia

<sup>1</sup> lingkan.gong@unswalumni.com
<sup>2</sup> odiessel@cse.unsw.edu.au

## Introduction ##

_**What is Dynamic Partial Reconfiguration**_

Due to the exponential increase in hardware design costs and risks of making customized chips, the electronics industry has begun shifting towards the use of reconfigurable devices such as Field Programmable Gate Arrays (FPGAs) as mainstream computing platforms. An FPGA is a special type of integrated circuit that can be programmed and reprogrammed with arbitrary logic function. Traditionally, an FPGA device is programmed when the system is powered up. Using Dynamic Partial Reconfiguration (DPR), or simply, partial reconfiguration, the programming and reprogramming of the FPGA can occur at system run time (aka. dynamic) and can be performed on selected parts of system (aka. partial).

Using DPR, a designer can map multiple reconfigurable hardware modules (RM) to a same physical reconfigurable region (RR) of the FPGA, and these RMs can be swapped at system run time. Therefore, a DPR design can time-multiplexed its submodules to adapt to changing execution requirements, and its design density is increased. Both major FPGA vendors, Xilinx and Altera, have supported DPR in their tool flows (See [Wikipedia](http://en.wikipedia.org/wiki/Partial_re-configuration), [Xilinx](http://www.xilinx.com/tools/partial-reconfiguration.htm), [Altera](http://www.altera.com/products/devices/stratix-fpgas/stratix-v/overview/partial-reconfiguration/stxv-part-reconfig.html)). However, vendor tools only support functional verification of a DRS design when it is _not_ reconfiguring. They do not yet support the simulation of the reconfiguration process itself.

_**What is `ReSim**_

**ReSim** is a reusable simulation library to support _cycle-accurate_ Register Transfer Level (RTL) simulation of a DRS design. It aims to assist designers in verifying integrated DRS designs BEFORE, DURING and AFTER partial reconfiguration. In particular

  * It supports _cycle-accurate_ simulation of the reconfiguration process, including the transfer of configuration bitstreams and the subsequent module swapping. The designers can debug all signal activities of a design while it is reconfiguring parts of its logic;
  * It supports designs described by RTL code (i.e., Verilog/VHDL);
  * It supports mainstream HDL simulators (e.g., ModelSim), and can be seamlessly integrated with FPGA vendor tools;
  * It has a comprehensive set of user documentation to get you started. See [Overview of ReSim(PPT)](http://code.google.com/p/resim-simulating-partial-reconfiguration/downloads/detail?name=resim_doc_ppt_v2_3b.ppt&can=2&q=) and [ReSim User Guide(PDF)](http://code.google.com/p/resim-simulating-partial-reconfiguration/downloads/detail?name=resim_doc_gettingstarted_v2_3b.pdf&can=2&q=);
  * It is proven to be effective by a comprehensive set of case studies. See [Our Success Stories](http://code.google.com/p/resim-simulating-partial-reconfiguration/#Success_Stories) and [ReSim Case Studies(PDF)](http://code.google.com/p/resim-simulating-partial-reconfiguration/downloads/detail?name=resim_doc_casestudies_v2_3b.pdf&can=2&q=);
  * It is free and is open source.

## Downloads ##

There are two ways to download the library. The easiest way is to download a zip/tar file. Click the "Source" Tab and select "Browse". Click either "zip" or "tar.gz" to download. See the following diagram as an example

<img src='http://wiki.resim-simulating-partial-reconfiguration.googlecode.com/git/Downloads/fig_gc_how_to_download.jpg' border='0' height='250'></img>

The second way is to use the GIT version control tool to checkout the library git repository. Click the "Source" Tab and select "Checkout".  Use the git command on that page to checkout the library source tree.

## Documentation ##

<table cellpadding='2' width='100%' border='0'>
<td width='70%' valign='top'>

<i><b>Functional Verification of Dynamically Reconfigurable FPGA-based Systems (Springer 2015)</b></i>

This book provides scientific background of the functional verification of DRS designs, as well as practical solutions as to how to use the ReSim/ReChannel libraries to simulate and verify a DRS design.<br>
<br>
<ul><li>Provides researchers with an in-depth understanding of the challenges in verifying dynamically reconfigurable systems and the state-of-the-art methods used to overcome them;<br>
</li><li>Guides engineers with systematic approaches and tools to achieve verification closure in their dynamically reconfigurable projects;<br>
</li><li>Includes a comprehensive set of case studies, with an analysis of real bugs detected in the designs described;<br>
</li><li>Uses tools and techniques compatible with mainstream products (e.g. Xilinx/Altera tools, ModelSim simulator, Verilog/VHDL design language, etc. …).</li></ul>

<a href='http://link.springer.com/book/10.1007%2F978-3-319-06838-1'>Get the book from Springer</a>

<a href='http://www.amazon.com/Functional-Verification-Dynamically-Reconfigurable-FPGA-based/dp/3319068377'>Get the book from Amazon</a>

</td>

<td width='30%' valign='top'>

<img src='http://wiki.resim-simulating-partial-reconfiguration.googlecode.com/git/Downloads/fig_gc_book.jpg' border='0' height='250'></img>

</td>
</table>

_**Online Documentation**_

  * [Overview of ReSim](ReSim.md)
  * [Overview of ReSim(PPT)](http://code.google.com/p/resim-simulating-partial-reconfiguration/downloads/detail?name=resim_doc_ppt_v2_3b.ppt&can=2&q=)
  * [ReSim User Guide(PDF)](http://code.google.com/p/resim-simulating-partial-reconfiguration/downloads/detail?name=resim_doc_gettingstarted_v2_3b.pdf&can=2&q=)
  * [ReSim Case Studies(PDF)](http://code.google.com/p/resim-simulating-partial-reconfiguration/downloads/detail?name=resim_doc_casestudies_v2_3b.pdf&can=2&q=)
  * [Published Papers and Reports](Published_Papers.md)
  * [Quick Start](Quick_Start.md)
  * [Steps For Using ReSim](Steps_For_Using_ReSim.md)
  * [Frequently Asked Questions](FAQ.md)
  * [Reference Manual](Reference_Manual.md)

<a href='Hidden comment: 
* [Trouble_Shooting Trouble Shooting]
'></a>

## Known Issues ##

See the ReSim page to understand the core idea and the primary limitation of the library.
See [Issues](http://code.google.com/p/resim-simulating-partial-reconfiguration/issues/list) for a list of bugs/defects. In particular, please refer to [issue 4](https://code.google.com/p/resim-simulating-partial-reconfiguration/issues/detail?id=4) to understand requirements on the ModelSim simulators.

## Success Stories ##

We demonstrate the value of `ReSim` and `ReSim`-based functional verification via various studies as summarized in the following table.

| Case Study | Design Complexity(LOC)<sup>1</sup> | Parameter Script(LOC)<sup>2</sup> | Simulation Overhead(%)<sup>3</sup> | DPR-related Bugs<sup>4</sup> ReSim/Others |
|:-----------|:-----------------------------------|:----------------------------------|:-----------------------------------|:------------------------------------------|
| XDRS (Streaming Application)| 1300(Verilog)+1150(C)              | 50                                | 8.3                                | 34/0                                      |
| XDRS (Periodic Application)| 1300(Verilog)+1750(C)              | 50                                | 6.8                                | 5/1                                       |
| Fault-tolerant Application | 2150(Verilog)                      | 60                                | 20.9                               | 18/4                                      |
| AutoVision | 1250(VHDL)+400(C)                  | 80                                | 1.7                                | 7                                         |
| Fast PCIe Configuration (XAPP883) | 3500(Verilog)                      | 150                               | 0.3                                | --                                        |
| Processor Peripheral (UG744) | 2400(VHDL)+3200(C)                 | 50                                | 0.7                                | --                                        |

  * NOTE 1: The Lines of Code (LOC) of the deesign only include reconfiguration machinery, which include modules that performs DPR (e.g. reconfiguration controller, isolation, etc) and software, if any, that controls DPR.
  * NOTE 2: The parameter script is the primary development overhead of using `ReSim` (See the [ReSim Overview](ReSim.md) page).
  * NOTE 3: Simulation overhead is measured from the profiling results of ModelSim.
  * NOTE 4: The bugs only include bugs in the reconfiguration machinery. The bugs are _real_ bugs detected in the development process instead of synthetic ones or false alarms.

The first is a in-house desgined, generic DRS computing platform, the XDRS system, to which we mapped two applications (i.e., a streaming application and a periodic application). Since the design was created from scratch, we found relatively large number of bugs in the reconfiguration machinery. A simplified version of this case study is included as an example of the release.

The second, fault-tolerant application uses DPR to recover from circuit faults introduced by radiation, and we aim to demonstrate verifying an in-house, non-processor based DRS system. We used ChipScope at the beginning of the project in order to compare ChipScope-based debugging with ReSim. We analyzed the bugs detected by ChipScope and found that all 4 bugs could easily have been detected via ReSim-based simulation.

Using a real world application, the AutoVision system, as our third case study, we then studied `ReSim`-based functional verification of cutting-edge, complex DRS designs. For the purpose of assessing `ReSim`, we modified the HW/SW of the original design. Our modification re-integrated various IPs from the original project, and `ReSim`-based simulation identified 7 DPR-related bugs in the integration process.

Finally, we applied `ReSim` to Xilinx reference designs. Although no bug was detected in vendor reference designs, as expected, simulating proven designs from the vendor demonstrated the robustness of `ReSim`. These two case studies are included as two examples of the release.

Details of these case studies can be found [HERE](http://code.google.com/p/resim-simulating-partial-reconfiguration/downloads/detail?name=resim_doc_casestudies_v2_3b.pdf&can=2&q=)


## Call for Testimonials ##

We are particularly interested in hearing from you. In particular, we are interested in knowing:

  * From your own usage experience, how would you comment on the learning curve of ReSim? Did you find it difficult to get started?
  * From your own usage experience, how would you comment on the overhead (simulation overhead & development overhead) of using ReSim with your own simulation environment?
  * How many DPR-related bugs were DETECTED using ReSim-based simulation? What were they?
  * How many DPR-related bugs were MISSED by ReSim-based simulation (and were detected by other methods or on the target FPGA)? What were they?
  * What is the complexity of the design under verification? How long the overall verification/simulation task took?

Apart from the above questions, any feedback from you is valuable to us. Please contact [Dr. Lingkan (George) Gong](Lingkan_Gong.md). Thank you very much.

## Call for Contributions ##

We are looking for perspective master's, PhD students to work on extending ReSim to
  * Support Vivado-based DRS design flow,
  * Support DRS designs on Virtex 7, Zynq, and Altera's Stratix-V FPGAs,
  * Support verifying fine-grained dynamic reconfiguration, and to
  * Support verifying module relocation.

By working on above projects, you are expected to gain practical FPGA design and verification skills. Please contact [Dr. Lingkan (George) Gong](Lingkan_Gong.md) or [Dr. Oliver Diessel](http://www.cse.unsw.edu.au/~odiessel/) for potential projects in these areas. Thank you very much.

## Acknowledgements ##

The researchers would like to thank Mr. Jens Hagemeyer from the University of Paderborn for his guidance on state restoration on Virtex-5 FPGAs. We also appreciate Mr. Johny Paul and Prof. Walter Stechele from the Technical University of Munich for providing the AutoVision design as an important case study for assessing ReSim. Lastly, we would like to thank Xilinx for their generous donations.



<img src='http://wiki.resim-simulating-partial-reconfiguration.googlecode.com/git/Downloads/fig_gc_logo.jpg' border='0' height='200'>