set str "[rsv_print_license]
`timescale 1ns/1ps

// The interface for reconfigurable region (rr). Each rr should have
// its own region interface type, although mutiple rr can share a same interface
// type as long as they have the same IOs.

[rsv_print_fpga $vf_ ri \n\n]

"
