onerror {resume}

do wave_mti.do
do coverageexclusions.do

## add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/stat_0/dummy_signal_0
## add wave -noupdate -expand -group rm -expand -group max_inter -radix hex /xdrs/region_0/rm0/stat_0/dummy_signal_1

## add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/stat_0/dummy_signal_0
## add wave -noupdate -expand -group rm -expand -group rev_inter -radix hex /xdrs/region_0/rm1/stat_0/dummy_signal_1

add wave -hex /xdrs/icapi_0/assert_icapi_wr_cdata
add wave -hex /xdrs/icapi_0/assert_icapi_rd_cdata
add wave -hex /xdrs/icapi_0/assert_icapi_baddr_bsize

## add wave -hex /xdrs/icapi_0/icap_0/assert_icap_if_cwe_n_stable
## add wave -hex /xdrs/icapi_0/icap_0/assert_icap_if_cdata_known
## add wave -hex /xdrs/icapi_0/icap_0/assert_icap_if_cdata_rb_known

add wave -hex /xdrs/assert_recon_if_sequence
add wave -hex /xdrs/assert_icapi_if_sequence

add wave -hex /xdrs/assert_pc_if_0_sequence
add wave -hex /xdrs/assert_pc_if_1_sequence
## add wave -hex /xdrs/assert_pc_if_0_data_hold
## add wave -hex /xdrs/assert_pc_if_1_data_hold

add wave -hex /xdrs/region_0/rm0/assert_maximum_operation
add wave -hex /xdrs/region_0/rm1/assert_reverse_operation
## add wave -hex /xdrs/region_0/rm0/assert_maximum_cfg_ack
## add wave -hex /xdrs/region_0/rm1/assert_reverse_cfg_ack

## add wave -hex /xdrs/region_0/rm0/cov_maximum_reset_0
## add wave -hex /xdrs/region_0/rm0/cov_maximum_reset_1
## add wave -hex /xdrs/region_0/rm0/cov_maximum_reset_2
## add wave -hex /xdrs/region_0/rm1/cov_reverse_reset_0
## add wave -hex /xdrs/region_0/rm1/cov_reverse_reset_1
## add wave -hex /xdrs/region_0/rm1/cov_reverse_reset_2

## atv log -asserts -enable /xdrs/assert_pc_if_0_sequence
## atv log -asserts -enable /xdrs/assert_pc_if_1_sequence
## atv log -asserts -enable /xdrs/assert_recon_if_sequence

## atv log -asserts -enable /xdrs/icapi_0/assert_icapi_wr_cdata
## atv log -asserts -enable /xdrs/icapi_0/assert_icapi_rd_cdata
