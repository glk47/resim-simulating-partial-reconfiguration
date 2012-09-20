
+define+SIMULATION
+incdir+./xapp883/sim

// XAPP883 FPC Top
//---------------------------------
./xapp883/hw/Source/Fast_PCIe_config_top.v
./xapp883/hw/Source/switcher.v
./xapp883/hw/Source/RM_startup.v

// XAPP883 8 Lane PCIe Endpoint
//---------------------------------
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_gtx_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/gtx_drp_chanalign_fix_3752_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/gtx_wrapper_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/gtx_rx_valid_filter_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/gtx_tx_sync_rate_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_bram_top_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_brams_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_bram_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_clocking_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_pipe_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_pipe_lane_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_pipe_misc_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_reset_delay_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_2_0_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/pcie_upconfig_fix_3451_v6.v
./xapp883/hw/Source/PCIe_x8_gen1/source/v6_pcie_v1_6.v


// XAPP883 PR_LOADER
//---------------------------------
./xapp883/hw/Source/pr_loader/pr_loader.v
./xapp883/hw/Source/pr_loader/PIO.v
./xapp883/hw/Source/pr_loader/PIO_64.v
./xapp883/hw/Source/pr_loader/PIO_EP.v
./xapp883/hw/Source/pr_loader/PIO_TO_CTRL.v
./xapp883/hw/Source/pr_loader/PIO_64_RX_ENGINE.v
./xapp883/hw/Source/pr_loader/PIO_64_TX_ENGINE.v
./xapp883/hw/Source/pr_loader/PIO_EP_MEM_ACCESS.v
./xapp883/hw/Source/pr_loader/config_FIFO.v
./xapp883/hw/Source/pr_loader/data_transfer.v
./xapp883/hw/Source/pr_loader/icap_access.v

// XAPP883 Application: Bus Master DMA
//---------------------------------
./xapp883/hw/Source/app/BMD_64_RX_ENGINE.v
./xapp883/hw/Source/app/BMD_64_TX_ENGINE.v
./xapp883/hw/Source/app/common/BMD_PCIE_20.v
./xapp883/hw/Source/app/common/BMD.v
./xapp883/hw/Source/app/common/BMD_GEN2.v
./xapp883/hw/Source/app/common/BMD_CFG_CTRL.v
./xapp883/hw/Source/app/common/BMD_EP.v
./xapp883/hw/Source/app/common/BMD_EP_MEM.v
./xapp883/hw/Source/app/common/BMD_EP_MEM_ACCESS.v
./xapp883/hw/Source/app/common/BMD_INTR_CTRL.v
./xapp883/hw/Source/app/common/BMD_INTR_CTRL_DELAY.v
./xapp883/hw/Source/app/common/BMD_RD_THROTTLE.v
./xapp883/hw/Source/app/common/BMD_TO_CTRL.v

// RTL source code modified  
//---------------------------------
./xapp883/hw/Source/pr_loader/icap_mod.v
./xapp883/hw/Source/app/v6_pci_exp_64b_app.v
./pcie_empty.v

