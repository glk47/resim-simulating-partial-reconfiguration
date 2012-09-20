
+define+BOARDx08
+define+SIM_USERTB
+define+SIMULATION
+incdir+.+./xapp883/sim

// Board Testbench
//--------------------------------------------
./xapp883/sim/board.v
./xapp883/sim/sys_clk_gen_ds.v
./xapp883/sim/sys_clk_gen.v

// Root Complex Model & Tests
//--------------------------------------------
./xapp883/sim/dsport/xilinx_pcie_2_0_rport_v6.v
./xapp883/sim/dsport/pcie_2_0_rport_v6.v
./xapp883/sim/dsport/pci_exp_usrapp_com.v
./xapp883/sim/dsport/pci_exp_usrapp_tx.v
./xapp883/sim/dsport/pci_exp_usrapp_cfg.v
./xapp883/sim/dsport/pci_exp_usrapp_rx.v
./xapp883/sim/dsport/pci_exp_usrapp_pl.v


