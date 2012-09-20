onerror {resume}

add wave -noupdate -format Logic -radix hex /xdrs/clk
add wave -noupdate -format Logic -radix hex /xdrs/rstn

add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/rc_start
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/rc_bop
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/rc_baddr
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/rc_bsize
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/rc_done
add wave -noupdate -expand -group icapi -radix ascii /xdrs/icapi_0/state_ascii
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/baddr
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/bsize

add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/ma_req
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/xbm_gnt
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/ma_select
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/ma_addr
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/ma_data
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/ma_rnw
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/xbm_ack
add wave -noupdate -expand -group icapi -radix hex /xdrs/icapi_0/xbm_data

add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cclk
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/ccs_n
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cwe_n
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cdata
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cbusy
add wave -noupdate -expand -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cdata_rb

add wave -noupdate -expand -group mgr -radix hex /xdrs/mgr_0/rc0_reqn
add wave -noupdate -expand -group mgr -radix hex /xdrs/mgr_0/rc0_ackn
add wave -noupdate -expand -group mgr -radix hex /xdrs/mgr_0/rc0_rstn
add wave -noupdate -expand -group mgr -radix hex /xdrs/mgr_0/rc0_reconfn
add wave -noupdate -expand -group mgr -radix hex /xdrs/mgr_0/rrid
add wave -noupdate -expand -group mgr -radix hex /xdrs/mgr_0/rmid

add wave -noupdate -expand -group pc -radix hex /xdrs/pc_0/ma_req
add wave -noupdate -expand -group pc -radix hex /xdrs/pc_0/xbm_gnt
add wave -noupdate -expand -group pc -radix hex /xdrs/pc_0/ma_select
add wave -noupdate -expand -group pc -radix hex /xdrs/pc_0/ma_addr
add wave -noupdate -expand -group pc -radix hex /xdrs/pc_0/ma_data
add wave -noupdate -expand -group pc -radix hex /xdrs/pc_0/ma_rnw
add wave -noupdate -expand -group pc -radix hex /xdrs/pc_0/xbm_ack
add wave -noupdate -expand -group pc -radix hex /xdrs/pc_0/xbm_data

add wave -noupdate -expand -group arbiter -radix ascii /xdrs/xbc_0/state_ascii
add wave -noupdate -expand -group arbiter -radix hex /xdrs/xbc_0/maid

add wave -noupdate -expand -group mem -radix hex /xdrs/mem_0/xbs_select
add wave -noupdate -expand -group mem -radix hex /xdrs/mem_0/xbs_addr
add wave -noupdate -expand -group mem -radix hex /xdrs/mem_0/xbs_data
add wave -noupdate -expand -group mem -radix hex /xdrs/mem_0/xbs_rnw
add wave -noupdate -expand -group mem -radix hex /xdrs/mem_0/sl_ack
add wave -noupdate -expand -group mem -radix hex /xdrs/mem_0/sl_data

add wave -noupdate -expand -group isolated -radix hex /xdrs/pc_0_prdy
add wave -noupdate -expand -group isolated -radix hex /xdrs/rr_0_crdy
add wave -noupdate -expand -group isolated -radix hex /xdrs/rr_0_cerr
add wave -noupdate -expand -group isolated -radix hex /xdrs/pc_0_data
add wave -noupdate -expand -group isolated -radix hex /xdrs/rr_0_prdy
add wave -noupdate -expand -group isolated -radix hex /xdrs/pc_0_crdy
add wave -noupdate -expand -group isolated -radix hex /xdrs/pc_0_cerr
add wave -noupdate -expand -group isolated -radix hex /xdrs/rr_0_data

add wave -noupdate -expand -group rr -radix hex /xdrs/region_0/p_prdy
add wave -noupdate -expand -group rr -radix hex /xdrs/region_0/p_crdy
add wave -noupdate -expand -group rr -radix hex /xdrs/region_0/p_cerr
add wave -noupdate -expand -group rr -radix hex /xdrs/region_0/p_data
add wave -noupdate -expand -group rr -radix hex /xdrs/region_0/c_prdy
add wave -noupdate -expand -group rr -radix hex /xdrs/region_0/c_crdy
add wave -noupdate -expand -group rr -radix hex /xdrs/region_0/c_cerr
add wave -noupdate -expand -group rr -radix hex /xdrs/region_0/c_data

add wave -noupdate -expand -group rm -expand -group max_io -radix hex /xdrs/region_0/rm0/clk
add wave -noupdate -expand -group rm -expand -group max_io -radix hex /xdrs/region_0/rm0/rstn
add wave -noupdate -expand -group rm -expand -group max_io -radix hex /xdrs/region_0/rm0/p_prdy
add wave -noupdate -expand -group rm -expand -group max_io -radix hex /xdrs/region_0/rm0/p_crdy
add wave -noupdate -expand -group rm -expand -group max_io -radix hex /xdrs/region_0/rm0/p_data
add wave -noupdate -expand -group rm -expand -group max_io -radix hex /xdrs/region_0/rm0/c_prdy
add wave -noupdate -expand -group rm -expand -group max_io -radix hex /xdrs/region_0/rm0/c_crdy
add wave -noupdate -expand -group rm -expand -group max_io -radix hex /xdrs/region_0/rm0/c_data
add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/data1
add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/data2
add wave -noupdate -expand -group rm -expand -group max_inter -radix ascii /xdrs/region_0/rm0/state_ascii
add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/retrycnt
add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/tocnt
add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/stat_0/outdata
add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/stat_0/outcnt
add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/stat_0/indata
add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/stat_0/incnt
add wave -noupdate -expand -group rm -expand -group max_sync -radix hex /xdrs/region_0/rm0/sync_0/rc_reqn
add wave -noupdate -expand -group rm -expand -group max_sync -radix hex /xdrs/region_0/rm0/sync_0/rc_ackn
add wave -noupdate -expand -group rm -expand -group max_sync -radix hex /xdrs/region_0/rm0/sync_0/state_c
add wave -noupdate -expand -group rm -expand -group max_sync -radix hex /xdrs/region_0/rm0/sync_0/rc_is_idle

add wave -noupdate -expand -group rm -expand -group rev_io -radix hex /xdrs/region_0/rm1/clk
add wave -noupdate -expand -group rm -expand -group rev_io -radix hex /xdrs/region_0/rm1/rstn
add wave -noupdate -expand -group rm -expand -group rev_io -radix hex /xdrs/region_0/rm1/p_prdy
add wave -noupdate -expand -group rm -expand -group rev_io -radix hex /xdrs/region_0/rm1/p_crdy
add wave -noupdate -expand -group rm -expand -group rev_io -radix hex /xdrs/region_0/rm1/p_data
add wave -noupdate -expand -group rm -expand -group rev_io -radix hex /xdrs/region_0/rm1/c_prdy
add wave -noupdate -expand -group rm -expand -group rev_io -radix hex /xdrs/region_0/rm1/c_crdy
add wave -noupdate -expand -group rm -expand -group rev_io -radix hex /xdrs/region_0/rm1/c_data
add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/data1
add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/data2
add wave -noupdate -expand -group rm -expand -group rev_inter -radix ascii /xdrs/region_0/rm1/state_ascii
add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/retrycnt
add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/tocnt
add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/stat_0/outdata
add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/stat_0/outcnt
add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/stat_0/indata
add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/stat_0/incnt
add wave -noupdate -expand -group rm -expand -group rev_sync -radix hex /xdrs/region_0/rm1/sync_0/rc_reqn
add wave -noupdate -expand -group rm -expand -group rev_sync -radix hex /xdrs/region_0/rm1/sync_0/rc_ackn
add wave -noupdate -expand -group rm -expand -group rev_sync -radix hex /xdrs/region_0/rm1/sync_0/state_c
add wave -noupdate -expand -group rm -expand -group rev_sync -radix hex /xdrs/region_0/rm1/sync_0/rc_is_idle
add wave -noupdate -expand -group rm -expand -group rev_sync -radix hex /xdrs/region_0/rm1/sync_0/rc_tc
