onerror {resume}

add wave -noupdate -group system -hex /board/sys_clk
add wave -noupdate -group system -hex /board/sys_reset

add wave -noupdate -hex -group bram -group splb 
add wave -noupdate -hex -group bram /board/system/xps_bram_if_cntlr_0/BRAM_Rst
add wave -noupdate -hex -group bram /board/system/xps_bram_if_cntlr_0/BRAM_Clk
add wave -noupdate -hex -group bram /board/system/xps_bram_if_cntlr_0/BRAM_EN
add wave -noupdate -hex -group bram /board/system/xps_bram_if_cntlr_0/BRAM_WEN
add wave -noupdate -hex -group bram /board/system/xps_bram_if_cntlr_0/BRAM_Addr
add wave -noupdate -hex -group bram /board/system/xps_bram_if_cntlr_0/BRAM_Din
add wave -noupdate -hex -group bram /board/system/xps_bram_if_cntlr_0/BRAM_Dout

add wave -noupdate -hex -group uart -group splb 
add wave -noupdate -hex -group uart /board/system/xps_uart_0/RX
add wave -noupdate -hex -group uart /board/system/xps_uart_0/TX
add wave -noupdate -hex -group uart /board/system/xps_uart_0/Interrupt

add wave -noupdate -hex -group intc -group splb 
add wave -noupdate -hex -group intc /board/system/xps_intc_0/xps_intc_0/intc_core_i/isr
add wave -noupdate -hex -group intc /board/system/xps_intc_0/xps_intc_0/intc_core_i/ipr
add wave -noupdate -hex -group intc /board/system/xps_intc_0/xps_intc_0/intc_core_i/ier
add wave -noupdate -hex -group intc /board/system/xps_intc_0/xps_intc_0/intc_core_i/iar
add wave -noupdate -hex -group intc /board/system/xps_intc_0/xps_intc_0/intc_core_i/sie
add wave -noupdate -hex -group intc /board/system/xps_intc_0/xps_intc_0/intc_core_i/cie
add wave -noupdate -hex -group intc /board/system/xps_intc_0/xps_intc_0/intc_core_i/ivr
add wave -noupdate -hex -group intc /board/system/xps_intc_0/xps_intc_0/intc_core_i/mer
add wave -noupdate -hex -group intc /board/system/xps_intc_0/Intr
add wave -noupdate -hex -group intc /board/system/xps_intc_0/Irq

add wave -noupdate -hex -group ppc440
add wave -noupdate -hex -group ppc440 -group pe32b 
add wave -noupdate -hex -group ppc440 -group mplb 
add wave -noupdate -hex -group ppc440 -group splb 
add wave -noupdate -hex -group ppc440 /board/system/ppc440_0/eicc440critirq
add wave -noupdate -hex -group ppc440 /board/system/ppc440_0/eicc440extirq

add wave -noupdate -hex -group math -group splb 
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/Bus2IP_Clk
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/Bus2IP_Reset
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/Bus2IP_WrCE 
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/Bus2IP_Data 
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/IP2Bus_WrAck
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/Bus2IP_BE   
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/Bus2IP_RdCE 
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/IP2Bus_Data 
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/IP2Bus_RdAck
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/slv_reg0        
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/slv_reg1        
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/result          
add wave -noupdate -hex -group math -group core /board/system/xps_math_0/xps_math_0/user_logic_i/statistic       

add wave -noupdate -hex -group math -group swreset /board/system/xps_math_0/xps_math_0/soft_reset_i/Bus2IP_Reset        
add wave -noupdate -hex -group math -group swreset /board/system/xps_math_0/xps_math_0/soft_reset_i/Bus2IP_Clk          
add wave -noupdate -hex -group math -group swreset /board/system/xps_math_0/xps_math_0/soft_reset_i/Bus2IP_WrCE         
add wave -noupdate -hex -group math -group swreset /board/system/xps_math_0/xps_math_0/soft_reset_i/Bus2IP_Data         
add wave -noupdate -hex -group math -group swreset /board/system/xps_math_0/xps_math_0/soft_reset_i/Bus2IP_BE           
add wave -noupdate -hex -group math -group swreset /board/system/xps_math_0/xps_math_0/soft_reset_i/Reset2IP_Reset      
add wave -noupdate -hex -group math -group swreset /board/system/xps_math_0/xps_math_0/soft_reset_i/Reset2Bus_WrAck     
add wave -noupdate -hex -group math -group swreset /board/system/xps_math_0/xps_math_0/soft_reset_i/Reset2Bus_Error     
add wave -noupdate -hex -group math -group swreset /board/system/xps_math_0/xps_math_0/soft_reset_i/Reset2Bus_ToutSup   

add wave -noupdate -hex -group math -group swclock /board/system/xps_math_0/xps_math_0/soft_clock_i/Bus2IP_Reset        
add wave -noupdate -hex -group math -group swclock /board/system/xps_math_0/xps_math_0/soft_clock_i/Bus2IP_Clk          
add wave -noupdate -hex -group math -group swclock /board/system/xps_math_0/xps_math_0/soft_clock_i/Bus2IP_WrCE         
add wave -noupdate -hex -group math -group swclock /board/system/xps_math_0/xps_math_0/soft_clock_i/Bus2IP_Data         
add wave -noupdate -hex -group math -group swclock /board/system/xps_math_0/xps_math_0/soft_clock_i/Bus2IP_BE           
add wave -noupdate -hex -group math -group swclock /board/system/xps_math_0/xps_math_0/soft_clock_i/Clk2IP_Clk      
add wave -noupdate -hex -group math -group swclock /board/system/xps_math_0/xps_math_0/soft_clock_i/Clk2Bus_WrAck     
add wave -noupdate -hex -group math -group swclock /board/system/xps_math_0/xps_math_0/soft_clock_i/Clk2Bus_Error     
add wave -noupdate -hex -group math -group swclock /board/system/xps_math_0/xps_math_0/soft_clock_i/Clk2Bus_ToutSup   

add wave -noupdate -hex -group math -group rm0 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm0/clk        
add wave -noupdate -hex -group math -group rm0 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm0/rst        
add wave -noupdate -hex -group math -group rm0 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm0/ain        
add wave -noupdate -hex -group math -group rm0 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm0/bin        
add wave -noupdate -hex -group math -group rm0 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm0/result     
add wave -noupdate -hex -group math -group rm0 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm0/statistic  
add wave -noupdate -hex -group math -group rm0 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm0/result_last

add wave -noupdate -hex -group math -group rm1 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm1/clk        
add wave -noupdate -hex -group math -group rm1 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm1/rst        
add wave -noupdate -hex -group math -group rm1 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm1/ain        
add wave -noupdate -hex -group math -group rm1 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm1/bin        
add wave -noupdate -hex -group math -group rm1 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm1/result     
add wave -noupdate -hex -group math -group rm1 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm1/statistic  
add wave -noupdate -hex -group math -group rm1 /board/system/xps_math_0/xps_math_0/user_logic_i/math_core_i/rm1/result_last

add wave -noupdate -hex -group icapctrl -group mplb 
add wave -noupdate -hex -group icapctrl -group splb 
add wave -noupdate -hex -group icapctrl /board/system/xps_icapi_0/IP2INTC_Irpt
if { [string first (xps_icapi) [find instances /board/system/xps_icapi_0/xps_icapi_0/]] != -1 } {
	#### FOR: XPS_ICAPI (RTL)
	add wave -noupdate -hex -group icapctrl -group regs /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_regs_0/m_ctrl
	add wave -noupdate -hex -group icapctrl -group regs /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_regs_0/m_stat
	add wave -noupdate -hex -group icapctrl -group regs /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_regs_0/m_bitstream_addr
	add wave -noupdate -hex -group icapctrl -group regs /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_regs_0/m_bitstream_size
	add wave -noupdate -hex -group icapctrl -group regs /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_regs_0/m_ier
	
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/rc_start
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/rc_bop
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/rc_baddr
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/rc_bsize
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/rc_done
	add wave -noupdate -ascii -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/state_ascii
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/baddr
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/bsize
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/cfg_data_wr_en
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/cfg_data
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/cfg_rdbk_wr_en
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/cfg_rdbk
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/ma_req
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/xbm_gnt
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/ma_select
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/ma_addr
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/ma_data
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/ma_rnw
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/ma_be
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/xbm_ack
	add wave -noupdate -hex -group icapctrl -group icapi /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/xbm_data
	
	add wave -noupdate -hex -group icapctrl -group masterif /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_masterif_0/master_rd_req
	add wave -noupdate -hex -group icapctrl -group masterif /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_masterif_0/master_wr_req
	add wave -noupdate -hex -group icapctrl -group masterif /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_masterif_0/master_address
	add wave -noupdate -hex -group icapctrl -group masterif /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_masterif_0/master_byte_enable
	add wave -noupdate -hex -group icapctrl -group masterif /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_masterif_0/master_rd_ack
	add wave -noupdate -hex -group icapctrl -group masterif /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_masterif_0/master_rd_data
	add wave -noupdate -hex -group icapctrl -group masterif /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_masterif_0/master_wr_ack
	add wave -noupdate -hex -group icapctrl -group masterif /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_masterif_0/master_wr_data
	add wave -noupdate -ascii -group icapctrl -group masterif /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_masterif_0/state_ascii
	
}
add wave -noupdate -hex -group icapctrl -group icap /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/icap_0/gen_resim/gen_virtex5/icap_virtex5_i/iif/cclk    
add wave -noupdate -hex -group icapctrl -group icap /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/icap_0/gen_resim/gen_virtex5/icap_virtex5_i/iif/ccs_n   
add wave -noupdate -hex -group icapctrl -group icap /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/icap_0/gen_resim/gen_virtex5/icap_virtex5_i/iif/cwe_n   
add wave -noupdate -hex -group icapctrl -group icap /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/icap_0/gen_resim/gen_virtex5/icap_virtex5_i/iif/cdata   
add wave -noupdate -hex -group icapctrl -group icap /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/icap_0/gen_resim/gen_virtex5/icap_virtex5_i/iif/cbusy   
add wave -noupdate -hex -group icapctrl -group icap /board/system/xps_icapi_0/xps_icapi_0/user_logic_i/icapi_0/icap_0/gen_resim/gen_virtex5/icap_virtex5_i/iif/cdata_rb

add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/SPLB_Clk
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/SPLB_Rst
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_PAValid
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_ABus
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_RNW
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_BE
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_size
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_type
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/Sl_addrAck
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/Sl_wait
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/Sl_rearbitrate
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_rdPrim
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_wrPrim
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_wrDBus
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_wrBurst
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/Sl_wrDAck
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/Sl_wrComp
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/Sl_rdDBus
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/Sl_rdWdAddr
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/PLB_rdBurst
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/Sl_rdDAck
add wave -noupdate -hex -group bram -group splb /board/system/xps_bram_if_cntlr_0/Sl_rdComp

add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/SPLB_Clk
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/SPLB_Rst
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_PAValid
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_ABus
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_RNW
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_BE
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_size
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_type
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/Sl_addrAck
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/Sl_wait
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/Sl_rearbitrate
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_rdPrim
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_wrPrim
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_wrDBus
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_wrBurst
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/Sl_wrDAck
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/Sl_wrComp
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/Sl_rdDBus
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/Sl_rdWdAddr
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/PLB_rdBurst
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/Sl_rdDAck
add wave -noupdate -hex -group intc -group splb /board/system/xps_intc_0/Sl_rdComp

add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/SPLB_Clk
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/SPLB_Rst
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_PAValid
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_ABus
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_RNW
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_BE
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_size
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_type
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/Sl_addrAck
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/Sl_wait
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/Sl_rearbitrate
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_rdPrim
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_wrPrim
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_wrDBus
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_wrBurst
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/Sl_wrDAck
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/Sl_wrComp
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/Sl_rdDBus
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/Sl_rdWdAddr
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/PLB_rdBurst
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/Sl_rdDAck
add wave -noupdate -hex -group uart -group splb /board/system/xps_uart_0/Sl_rdComp

add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/SPLB_Clk      
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/SPLB_Rst      
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_PAValid   
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_ABus      
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_RNW       
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_BE        
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_size      
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_type      
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/Sl_addrAck    
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/Sl_wait       
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/Sl_rearbitrate
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_rdPrim    
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_wrPrim    
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_wrDBus    
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_wrBurst   
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/Sl_wrDAck     
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/Sl_wrComp     
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/Sl_rdDBus     
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/Sl_rdWdAddr   
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/PLB_rdBurst   
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/Sl_rdDAck     
add wave -noupdate -hex -group math -group splb /board/system/xps_math_0/Sl_rdComp     

if { [string first (xps_icapi) [find instances /board/system/xps_icapi_0/xps_icapi_0/]] != -1 } {
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/MPLB_Clk
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/MPLB_Rst
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/M_request
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/M_ABus
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/M_RNW
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/M_BE
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/M_size
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/M_type
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/PLB_MAddrAck
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/M_wrDBus
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/M_wrBurst
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/PLB_MWrDAck
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/PLB_MRdDBus
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/PLB_MRdWdAddr
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/M_rdBurst
	add wave -noupdate -hex -group icapctrl -group mplb /board/system/xps_icapi_0/PLB_MRdDAck
}

add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/SPLB_Clk
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/SPLB_Rst
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_PAValid
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_ABus
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_RNW
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_BE
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_size
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_type
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/Sl_addrAck
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/Sl_wait
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/Sl_rearbitrate
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_rdPrim
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_wrPrim
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_wrDBus
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_wrBurst
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/Sl_wrDAck
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/Sl_wrComp
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/Sl_rdDBus
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/Sl_rdWdAddr
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/PLB_rdBurst
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/Sl_rdDAck
add wave -noupdate -hex -group icapctrl -group splb /board/system/xps_icapi_0/Sl_rdComp 

add wave -noupdate -hex -group ppc440 /board/system/ppc440_0/cpmc440clk
add wave -noupdate -hex -group ppc440 /board/system/ppc440_0/rstC440resetCore
add wave -noupdate -hex -group ppc440 /board/system/ppc440_0/rstC440resetChip
add wave -noupdate -hex -group ppc440 /board/system/ppc440_0/rstC440resetSystem

add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/ppcMPLBrequest
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/ppcMPLBABus
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/ppcMPLBRNW
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/ppcMPLBBE
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/ppcMPLBsize
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/ppcMPLBtype
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/PLBppcmAddrAck
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/ppcMPLBwrDBus
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/ppcMPLBwrBurst
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/PLBppcmWrDAck
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/PLBppcmRdDBus
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/PLBppcmRdWdAddr
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/ppcMPLBrdBurst
add wave -noupdate -hex -group ppc440 -group mplb /board/system/ppc440_0/PLBppcmRdDAck

add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0PAValid
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0ABus
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0RNW
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0BE
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0size
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0type
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PPCs0plbaddrAck
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PPCs0plbwait
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PPCs0plbrearbitrate
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0rdPrim
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0wrPrim
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0wrDBus
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0wrBurst
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PPCs0plbwrDAck
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PPCs0plbwrComp
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PPCs0plbrdDBus
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PPCs0plbrdWdAddr
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PLBppcs0rdBurst
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PPCs0plbrdDAck
add wave -noupdate -hex -group ppc440 -group splb /board/system/ppc440_0/PPCs0plbrdComp

add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR3
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR4
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR5
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR6
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR7
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR8
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR9
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR10
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR11
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR12
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR13
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR14
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR15
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR16
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR17
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR18
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR19
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR20
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR21
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR22
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR23
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR24
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR25
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR26
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR27
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR28
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR29
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR30
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/GPR31
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SPRG0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SPRG1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SPRG2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SPRG3
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SPRG4
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SPRG5
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SPRG6
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SPRG7
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/CR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/CTR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DEC
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DECAR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/ESR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/TBL
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/TBU
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/LR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/CCR0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/CSRR0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/CSRR1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DBCR0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DBCR1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DBCR2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DBSR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IAC1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IAC2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IAC3
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IAC4
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR3
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR4
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR5
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR6
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR7
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR8
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR9
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR10
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR11
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR12
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR13
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR14
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVOR15
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVPR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/MMUCR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/MSR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/MCSR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/PID
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SRR0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/SRR1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/MCSRR0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/MCSRR1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/TCR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/TSR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/XER
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/CCR1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DAC1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DAC2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DBDR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DCDBTRH
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DCDBTRL
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DEAR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DNV0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DNV1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DNV2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DNV3
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DTV0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DTV1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DTV2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DTV3
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DVC1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DVC2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DVLIM
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/ICDBDR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/ICDBTRH
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/ICDBTRL
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/INV0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/INV1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/INV2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/INV3
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/ITV0
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/ITV1
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/ITV2
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/ITV3
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IVLIM
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/PIR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/PVR
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/RSTCFG
add wave -noupdate -hex -group ppc440 -group pe32b /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/USPRG0

add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IFAR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/STOPACK
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/PFTHADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DISS3ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DISS2ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DISS1ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/DISS0ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IRACCADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IEXE1ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IEXE2ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/IWBADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/LRACCADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/AGENADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/CRDADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/LWBADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/JEXE1ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/JEXE2ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/JWBADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/PDCD0ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/PDCD1ADDR
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/PDCD0DATA
add wave -noupdate -hex -group ppc440 -group internal /board/system/ppc440_0/ppc440_0/PPC440_i/ppc440_swift_1/PDCD1DATA

add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mc_mibclk
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mi_mcreset
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mc_miaddrreadytoaccept
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mi_mcaddress
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mi_mcaddressvalid
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mi_mcreadnotwrite
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mi_mcbyteenable
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mi_mcbankconflict
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mi_mcrowconflict
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mi_mcwritedata
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mi_mcwritedatavalid
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mc_mireaddata
add wave -noupdate -hex -group ddr2 -group mimc /board/system/ddr2_sdram_0/mc_mireaddatavalid
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_CK\[0\]
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_CKE
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_CS_N
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_A
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_BA
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_WE_N
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_RAS_N
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_CAS_N
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_DQ
add wave -noupdate -hex -group ddr2 -group memory /board/system/ddr2_sdram_0/DDR2_DM
