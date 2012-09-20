onerror {resume}

#=============================
# Global signals
#=============================

add wave -noupdate -radix hex /board/PR_top/sys_reset_n_c
add wave -noupdate -radix hex /board/PR_top/sys_clk_c

#=============================
# LogiCORE PCIe Endpoint
#=============================

add wave -noupdate -radix hex -group endpoint /board/PR_top/trn_reset_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/trn_clk
add wave -noupdate -radix hex -group endpoint /board/PR_top/trn_lnk_up_n

add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_tsrc_rdy_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_tdst_rdy_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_td
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_trem_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_rsrc_dsc_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_tsof_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_teof_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_tbuf_av

add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_rsrc_rdy_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_rdst_rdy_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_rd
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_rrem_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_rsrc_dsc_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_rsof_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_reof_n
add wave -noupdate -radix hex -group endpoint /board/PR_top/core/trn_rbar_hit_n

add wave -noupdate -radix hex -group endpoint -group flowctrl /board/PR_top/core/trn_fc_cpld
add wave -noupdate -radix hex -group endpoint -group flowctrl /board/PR_top/core/trn_fc_cplh
add wave -noupdate -radix hex -group endpoint -group flowctrl /board/PR_top/core/trn_fc_npd
add wave -noupdate -radix hex -group endpoint -group flowctrl /board/PR_top/core/trn_fc_nph
add wave -noupdate -radix hex -group endpoint -group flowctrl /board/PR_top/core/trn_fc_pd
add wave -noupdate -radix hex -group endpoint -group flowctrl /board/PR_top/core/trn_fc_ph
add wave -noupdate -radix hex -group endpoint -group flowctrl /board/PR_top/core/trn_fc_sel

add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_do
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_rd_wr_done_n
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_di
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_byte_en_n
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_dwaddr
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_wr_en_n
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_rd_en_n
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_interrupt_n
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_interrupt_rdy_n
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_interrupt_assert_n
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_to_turnoff_n
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_turnoff_ok_n
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_bus_number
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_device_number
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_function_number
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_status
add wave -noupdate -radix hex -group endpoint -group configuration /board/PR_top/core/cfg_command

#=============================
# PR_LOADER
#=============================

add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_reset_n
add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_clk

add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_tsrc_rdy_n
add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_tdst_rdy_n
add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_td
add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_trem_n
add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_rsrc_dsc_n
add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_tsof_n
add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_teof_n

#### add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_tbuf_av
#### add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/trn_tdst_dsc_n

add wave -noupdate -group loader -radix hex /board/PR_top/pr_loader_i/PIO/trn_rsrc_rdy_n
add wave -noupdate -group loader -radix hex /board/PR_top/pr_loader_i/PIO/trn_rdst_rdy_n
add wave -noupdate -group loader -radix hex /board/PR_top/pr_loader_i/PIO/trn_rd
add wave -noupdate -group loader -radix hex /board/PR_top/pr_loader_i/PIO/trn_rrem_n
add wave -noupdate -group loader -radix hex /board/PR_top/pr_loader_i/PIO/trn_rsrc_dsc_n
add wave -noupdate -group loader -radix hex /board/PR_top/pr_loader_i/PIO/trn_rsof_n
add wave -noupdate -group loader -radix hex /board/PR_top/pr_loader_i/PIO/trn_reof_n
add wave -noupdate -group loader -radix hex /board/PR_top/pr_loader_i/PIO/trn_rbar_hit_n

add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/cfg_to_turnoff_n
add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/cfg_turnoff_ok_n
add wave -noupdate -radix hex -group loader /board/PR_top/pr_loader_i/PIO/pr_done

add wave -noupdate -radix ascii -group loader -group EP_RX /board/PR_top/pr_loader_i/PIO/PIO_EP/EP_RX/state_ascii
add wave -noupdate -radix hex -group loader -group EP_RX /board/PR_top/pr_loader_i/PIO/PIO_EP/EP_RX/wr_addr_o
add wave -noupdate -radix hex -group loader -group EP_RX /board/PR_top/pr_loader_i/PIO/PIO_EP/EP_RX/wr_be_o
add wave -noupdate -radix hex -group loader -group EP_RX /board/PR_top/pr_loader_i/PIO/PIO_EP/EP_RX/wr_data_o
add wave -noupdate -radix hex -group loader -group EP_RX /board/PR_top/pr_loader_i/PIO/PIO_EP/EP_RX/wr_en_o
add wave -noupdate -radix hex -group loader -group EP_RX /board/PR_top/pr_loader_i/PIO/PIO_EP/EP_RX/wr_busy_i

add wave -noupdate -radix hex -group loader -group EP_DXFR -label pcie_clk /board/PR_top/pr_loader_i/PIO/PIO_EP/data_transfer_i/PCIe_CLK
add wave -noupdate -radix hex -group loader -group EP_DXFR -label fifo_wr_en_i /board/PR_top/pr_loader_i/PIO/PIO_EP/data_transfer_i/WR_RQST
add wave -noupdate -radix hex -group loader -group EP_DXFR -label fifo_wr_data_i /board/PR_top/pr_loader_i/PIO/PIO_EP/data_transfer_i/WR_DATA
add wave -noupdate -radix hex -group loader -group EP_DXFR -label fifo_prog_full_o /board/PR_top/pr_loader_i/PIO/PIO_EP/data_transfer_i/PAUSE
add wave -noupdate -radix hex -group loader -group EP_DXFR -label conf_clk /board/PR_top/pr_loader_i/PIO/PIO_EP/data_transfer_i/CONF_CLK
add wave -noupdate -radix hex -group loader -group EP_DXFR -label conf_enable_o /board/PR_top/pr_loader_i/PIO/PIO_EP/data_transfer_i/CONF_ENABLE
add wave -noupdate -radix hex -group loader -group EP_DXFR -label conf_data_o /board/PR_top/pr_loader_i/PIO/PIO_EP/data_transfer_i/CONF_DATA

add wave -noupdate -radix hex -group loader -group ICAP_V6 /board/PR_top/pr_loader_i/PIO/PIO_EP/ICAP_ACC/ICAP/ICAP_VIRTEX6_I/iif/cclk     
add wave -noupdate -radix hex -group loader -group ICAP_V6 /board/PR_top/pr_loader_i/PIO/PIO_EP/ICAP_ACC/ICAP/ICAP_VIRTEX6_I/iif/cwe_n    
add wave -noupdate -radix hex -group loader -group ICAP_V6 /board/PR_top/pr_loader_i/PIO/PIO_EP/ICAP_ACC/ICAP/ICAP_VIRTEX6_I/iif/ccs_n    
add wave -noupdate -radix hex -group loader -group ICAP_V6 /board/PR_top/pr_loader_i/PIO/PIO_EP/ICAP_ACC/ICAP/ICAP_VIRTEX6_I/iif/cdata    
add wave -noupdate -radix hex -group loader -group ICAP_V6 /board/PR_top/pr_loader_i/PIO/PIO_EP/ICAP_ACC/ICAP/ICAP_VIRTEX6_I/iif/cbusy    
add wave -noupdate -radix hex -group loader -group ICAP_V6 /board/PR_top/pr_loader_i/PIO/PIO_EP/ICAP_ACC/ICAP/ICAP_VIRTEX6_I/iif/cdata_rb 

#=============================
# User Application: Bus Master DMA
#=============================

add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_reset_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_clk

add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_tsrc_rdy_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_tdst_rdy_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_td
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_trem_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_rsrc_dsc_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_tsof_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_teof_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_tbuf_av
#### ??destination disconnect?? trn_tdst_dsc_n
#### add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_tdst_dsc_n

add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_rsrc_rdy_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_rdst_rdy_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_rd
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_rrem_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_rsrc_dsc_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_rsof_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_reof_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/trn_rbar_hit_n

add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/cfg_to_turnoff_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/BMD/cfg_turnoff_ok_n
add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm1/RM_rdy_sig

#=============================
# User Application: Empty Module on Power up
#=============================

add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_reset_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_clk

add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_tsrc_rdy_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_tdst_rdy_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_td
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_trem_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_rsrc_dsc_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_tsof_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_teof_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_tbuf_av
#### ??destination disconnect?? trn_tdst_dsc_n
#### add wave -noupdate -radix hex -group bmdma /board/PR_top/app/rm0/trn_tdst_dsc_n

add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_rsrc_rdy_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_rdst_rdy_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_rd
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_rrem_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_rsrc_dsc_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_rsof_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_reof_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/trn_rbar_hit_n

add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/cfg_to_turnoff_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm0/cfg_turnoff_ok_n
add wave -noupdate -radix hex -group empty /board/PR_top/app/rm1/RM_rdy_sig

#=============================
# RM Startup
#=============================

add wave -noupdate -radix hex -group startup /board/PR_top/RM_startup_i/manual_partition_sw
add wave -noupdate -radix hex -group startup /board/PR_top/RM_startup_i/pr_done
add wave -noupdate -radix hex -group startup /board/PR_top/RM_startup_i/RM_trn_reset_n
add wave -noupdate -radix hex -group startup /board/PR_top/RM_startup_i/static_control
add wave -noupdate -radix hex -group startup /board/PR_top/RM_startup_i/RM_rdy_sig


