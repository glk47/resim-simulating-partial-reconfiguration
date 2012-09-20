
source settings.do; 

namespace import ReSim::*

rsv_create_portmap "pcie_if" "trn_clk"

rsv_add_port "pcie_if" "trn_reset_n"       in  
rsv_add_port "pcie_if" "trn_lnk_up_n"      in  

rsv_add_port "pcie_if" "trn_tbuf_av"       in  6     
rsv_add_port "pcie_if" "trn_tcfg_req_n"    in        
rsv_add_port "pcie_if" "trn_terr_drop_n"   in        
rsv_add_port "pcie_if" "trn_tdst_rdy_n"    in        
rsv_add_port "pcie_if" "trn_td"            out 64
rsv_add_port "pcie_if" "trn_trem_n"        out       
rsv_add_port "pcie_if" "trn_tsof_n"        out       
rsv_add_port "pcie_if" "trn_teof_n"        out       
rsv_add_port "pcie_if" "trn_tsrc_rdy_n"    out       
rsv_add_port "pcie_if" "trn_tsrc_dsc_n"    out       
rsv_add_port "pcie_if" "trn_terrfwd_n"     out       
rsv_add_port "pcie_if" "trn_tcfg_gnt_n"    out       
rsv_add_port "pcie_if" "trn_tstr_n"        out       

rsv_add_port "pcie_if" "trn_rd"            in  64    
rsv_add_port "pcie_if" "trn_rrem_n"        in        
rsv_add_port "pcie_if" "trn_rsof_n"        in        
rsv_add_port "pcie_if" "trn_reof_n"        in        
rsv_add_port "pcie_if" "trn_rsrc_rdy_n"    in        
rsv_add_port "pcie_if" "trn_rsrc_dsc_n"    in        
rsv_add_port "pcie_if" "trn_rerrfwd_n"     in        
rsv_add_port "pcie_if" "trn_rbar_hit_n"    in  7     
rsv_add_port "pcie_if" "trn_rdst_rdy_n"    out       
rsv_add_port "pcie_if" "trn_rnp_ok_n"      out       
rsv_add_port "pcie_if" "trn_fc_sel"        out 3  

rsv_add_port "pcie_if" "cfg_do"            in  32   
rsv_add_port "pcie_if" "cfg_rd_wr_done_n"  in       
rsv_add_port "pcie_if" "cfg_di"            out 32   
rsv_add_port "pcie_if" "cfg_byte_en_n"     out 4    
rsv_add_port "pcie_if" "cfg_dwaddr"        out 10   
rsv_add_port "pcie_if" "cfg_wr_en_n"       out      
rsv_add_port "pcie_if" "cfg_rd_en_n"       out      

rsv_add_port "pcie_if" "cfg_err_cor_n"            out       
rsv_add_port "pcie_if" "cfg_err_ur_n"             out       
rsv_add_port "pcie_if" "cfg_err_ecrc_n"           out       
rsv_add_port "pcie_if" "cfg_err_cpl_timeout_n"    out       
rsv_add_port "pcie_if" "cfg_err_cpl_abort_n"      out       
rsv_add_port "pcie_if" "cfg_err_cpl_unexpect_n"   out       
rsv_add_port "pcie_if" "cfg_err_posted_n"         out       
rsv_add_port "pcie_if" "cfg_err_locked_n"         out       
rsv_add_port "pcie_if" "cfg_err_tlp_cpl_header"   out 48    

rsv_add_port "pcie_if" "cfg_interrupt_n"          out       
rsv_add_port "pcie_if" "cfg_interrupt_rdy_n"      in        
rsv_add_port "pcie_if" "cfg_interrupt_assert_n"   out       
rsv_add_port "pcie_if" "cfg_interrupt_di"         out 8     
rsv_add_port "pcie_if" "cfg_interrupt_do"         in  8     
rsv_add_port "pcie_if" "cfg_interrupt_mmenable"   in  3     
rsv_add_port "pcie_if" "cfg_interrupt_msienable"  in        
rsv_add_port "pcie_if" "cfg_interrupt_msixenable" in        
rsv_add_port "pcie_if" "cfg_interrupt_msixfm"     in        

rsv_add_port "pcie_if" "cfg_turnoff_ok_n"         out       
rsv_add_port "pcie_if" "cfg_to_turnoff_n"         in        
rsv_add_port "pcie_if" "cfg_trn_pending_n"        out       
rsv_add_port "pcie_if" "cfg_pm_wake_n"            out       
rsv_add_port "pcie_if" "cfg_bus_number"           in  8     
rsv_add_port "pcie_if" "cfg_device_number"        in  5     
rsv_add_port "pcie_if" "cfg_function_number"      in  3     
rsv_add_port "pcie_if" "cfg_command"              in  16    
rsv_add_port "pcie_if" "cfg_dcommand"             in  16    
rsv_add_port "pcie_if" "cfg_lstatus"              in  16    
rsv_add_port "pcie_if" "cfg_lcommand"             in  16    
rsv_add_port "pcie_if" "cfg_dsn"                  out 64    

rsv_add_port "pcie_if" "RM_rdy_sig"               out 32    

rsv_create_region "pcie_app_v6" "pcie_if" 20

rsv_add_module "pcie_app_v6" "pcie_empty" ""
rsv_add_module "pcie_app_v6" "pcie_bmdma" ""

rsv_create_solyr "pcie_solayer" VIRTEX6

rsv_add_region "pcie_solayer" "pcie_app_v6"
rsv_gen_solyr  "pcie_solayer"

rsv_create_memory "mem" 4 1 be

rsv_add_2_memory "mem" "./artifacts/sbt/pcie_app_v6_rm0.sbt"  0x000
rsv_add_2_memory "mem" "./artifacts/sbt/pcie_app_v6_rm1.sbt"  0x100

namespace forget ReSim::*
