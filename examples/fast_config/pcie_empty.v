
`timescale 1ns / 1ps

// To use RESIM
// ================================================
// Add this new file
module  pcie_empty
(

  input                                          trn_clk,
  input                                          trn_reset_n,
  input                                          trn_lnk_up_n, 

  // Tx
  input  [5:0]                                   trn_tbuf_av,
  input                                          trn_tcfg_req_n,
  input                                          trn_terr_drop_n,
  input                                          trn_tdst_rdy_n,
  output [63:0]                                  trn_td,
  output                                         trn_trem_n,
  output                                         trn_tsof_n,
  output                                         trn_teof_n,
  output                                         trn_tsrc_rdy_n,
  output                                         trn_tsrc_dsc_n,
  output                                         trn_terrfwd_n,
  output                                         trn_tcfg_gnt_n,
  output                                         trn_tstr_n,

  // Rx
  input  [63:0]                                  trn_rd,
  input                                          trn_rrem_n,
  input                                          trn_rsof_n,
  input                                          trn_reof_n,
  input                                          trn_rsrc_rdy_n,
  input                                          trn_rsrc_dsc_n,
  input                                          trn_rerrfwd_n,
  input  [6:0]                                   trn_rbar_hit_n,
  output                                         trn_rdst_rdy_n,
  output                                         trn_rnp_ok_n, 
  output [2:0]                                   trn_fc_sel,


  input  [31:0]                                  cfg_do,
  input                                          cfg_rd_wr_done_n,
  output [31:0]                                  cfg_di,
  output [3:0]                                   cfg_byte_en_n,
  output [9:0]                                   cfg_dwaddr,
  output                                         cfg_wr_en_n,
  output                                         cfg_rd_en_n,


  output                                         cfg_err_cor_n,
  output                                         cfg_err_ur_n,
  output                                         cfg_err_ecrc_n,
  output                                         cfg_err_cpl_timeout_n,
  output                                         cfg_err_cpl_abort_n,
  output                                         cfg_err_cpl_unexpect_n,
  output                                         cfg_err_posted_n,
  output                                         cfg_err_locked_n,
  output [47:0]                                  cfg_err_tlp_cpl_header,
//  input                                          cfg_err_cpl_rdy_n,
  output                                         cfg_interrupt_n,
  input                                          cfg_interrupt_rdy_n,
  output                                         cfg_interrupt_assert_n,
  output [7:0]                                   cfg_interrupt_di,
  input  [7:0]                                   cfg_interrupt_do,
  input  [2:0]                                   cfg_interrupt_mmenable,
  input                                          cfg_interrupt_msienable,
  input                                          cfg_interrupt_msixenable,
  input                                          cfg_interrupt_msixfm,
  output                                         cfg_turnoff_ok_n,
  input                                          cfg_to_turnoff_n,
  output                                         cfg_trn_pending_n,
  output                                         cfg_pm_wake_n,
  input   [7:0]                                  cfg_bus_number,
  input   [4:0]                                  cfg_device_number,
  input   [2:0]                                  cfg_function_number,
//  input  [15:0]                                  cfg_status,
  input  [15:0]                                  cfg_command,
//  input  [15:0]                                  cfg_dstatus,
  input  [15:0]                                  cfg_dcommand,
  input  [15:0]                                  cfg_lstatus,
  input  [15:0]                                  cfg_lcommand,
//  input  [15:0]                                  cfg_dcommand2,
//  input   [2:0]                                  cfg_pcie_link_state_n,
  output [63:0]                                  cfg_dsn,
`ifdef Chipscope  
    output [80:0]        TRIG_BMD_TX,
    output [90:0]        TRIG_BMD_RX,
`endif  
  output reg [31:0]                              RM_rdy_sig 

);


endmodule // pcie_app
