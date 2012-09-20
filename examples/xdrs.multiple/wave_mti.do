onerror {resume}

add wave -noupdate -format Logic -radix hex /xdrs/clk
add wave -noupdate -format Logic -radix hex /xdrs/rstn

add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/rc_start
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/rc_bop
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/rc_baddr
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/rc_bsize
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/rc_done
add wave -noupdate -group icapi -radix ascii /xdrs/icapi_0/state_ascii
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/baddr
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/bsize

add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/ma_req
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/xbm_gnt
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/ma_select
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/ma_addr
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/ma_data
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/ma_rnw
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/xbm_ack
add wave -noupdate -group icapi -radix hex /xdrs/icapi_0/xbm_data

add wave -noupdate -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cclk
add wave -noupdate -group icap -radix hex /xdrs/icapi_0/icap_0/iif/ccs_n
add wave -noupdate -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cwe_n
add wave -noupdate -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cdata
add wave -noupdate -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cbusy
add wave -noupdate -group icap -radix hex /xdrs/icapi_0/icap_0/iif/cdata_rb

add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc0_reqn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc0_ackn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc0_rstn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc0_reconfn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc1_reqn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc1_ackn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc1_rstn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc1_reconfn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc2_reqn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc2_ackn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc2_rstn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rc2_reconfn
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rrid
add wave -noupdate -group mgr -radix hex /xdrs/mgr_0/rmid

add wave -noupdate -group arbiter -radix ascii /xdrs/xbc_0/state_ascii
add wave -noupdate -group arbiter -radix hex /xdrs/xbc_0/maid

add wave -noupdate -group mem -radix hex /xdrs/mem_0/xbs_select
add wave -noupdate -group mem -radix hex /xdrs/mem_0/xbs_addr
add wave -noupdate -group mem -radix hex /xdrs/mem_0/xbs_data
add wave -noupdate -group mem -radix hex /xdrs/mem_0/xbs_rnw
add wave -noupdate -group mem -radix hex /xdrs/mem_0/sl_ack
add wave -noupdate -group mem -radix hex /xdrs/mem_0/sl_data

add wave -noupdate -group rr0 -radix hex /xdrs/region_0/clk
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/rstn
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/p_prdy
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/p_crdy
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/p_data
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/p_cerr
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/c_prdy
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/c_crdy
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/c_data
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/c_cerr
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/rc_reqn
add wave -noupdate -group rr0 -radix hex /xdrs/region_0/rc_ackn

add wave -noupdate -group rr0 -group max_inter -radix hex /xdrs/region_0/gen_rr/gen_0/math_0/rm0/data1
add wave -noupdate -group rr0 -group max_inter -radix hex /xdrs/region_0/gen_rr/gen_0/math_0/rm0/data2
add wave -noupdate -group rr0 -group max_inter -radix ascii /xdrs/region_0/gen_rr/gen_0/math_0/rm0/state_ascii
add wave -noupdate -group rr0 -group rev_inter -radix hex /xdrs/region_0/gen_rr/gen_0/math_0/rm1/data1
add wave -noupdate -group rr0 -group rev_inter -radix hex /xdrs/region_0/gen_rr/gen_0/math_0/rm1/data2
add wave -noupdate -group rr0 -group rev_inter -radix ascii /xdrs/region_0/gen_rr/gen_0/math_0/rm1/state_ascii

add wave -noupdate -group rr1 -radix hex /xdrs/region_1/clk
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/rstn
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/p_prdy
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/p_crdy
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/p_data
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/p_cerr
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/c_prdy
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/c_crdy
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/c_data
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/c_cerr
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/rc_reqn
add wave -noupdate -group rr1 -radix hex /xdrs/region_1/rc_ackn

add wave -noupdate -group rr1 -group max_inter -radix hex /xdrs/region_1/gen_rr/gen_1/math_1/rm0/data1
add wave -noupdate -group rr1 -group max_inter -radix hex /xdrs/region_1/gen_rr/gen_1/math_1/rm0/data2
add wave -noupdate -group rr1 -group max_inter -radix ascii /xdrs/region_1/gen_rr/gen_1/math_1/rm0/state_ascii
add wave -noupdate -group rr1 -group rev_inter -radix hex /xdrs/region_1/gen_rr/gen_1/math_1/rm1/data1
add wave -noupdate -group rr1 -group rev_inter -radix hex /xdrs/region_1/gen_rr/gen_1/math_1/rm1/data2
add wave -noupdate -group rr1 -group rev_inter -radix ascii /xdrs/region_1/gen_rr/gen_1/math_1/rm1/state_ascii

add wave -noupdate -group rr2 -radix hex /xdrs/region_2/clk
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/rstn
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/p_prdy
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/p_crdy
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/p_data
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/p_cerr
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/c_prdy
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/c_crdy
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/c_data
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/c_cerr
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/rc_reqn
add wave -noupdate -group rr2 -radix hex /xdrs/region_2/rc_ackn

add wave -noupdate -group rr2 -group mac_inter -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0/gen_lpfir/gen_mac/fir/*
add wave -noupdate -group rr2 -group mac_inter -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0/gen_lpfir/gen_mac/fir/X_reg
add wave -noupdate -group rr2 -group mac_sync  -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0/sync_0/state_c
add wave -noupdate -group rr2 -group mac_sync  -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0/sync_0/synccnt
add wave -noupdate -group rr2 -group mac_sync  -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0/sync_0/is_end_sync
add wave -noupdate -group rr2 -group mac_sync  -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0/sync_0/start_sync
add wave -noupdate -group rr2 -group tf_inter  -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1/gen_lpfir/gen_tf/fir/*
add wave -noupdate -group rr2 -group tf_inter  -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1/gen_lpfir/gen_tf/fir/X_reg
add wave -noupdate -group rr2 -group tf_sync   -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1/sync_0/state_c
add wave -noupdate -group rr2 -group tf_sync   -radix hex /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1/sync_0/synccnt
