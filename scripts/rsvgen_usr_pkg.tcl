set str "[rsv_print_license]

package usr_solyr_pkg;

	timeunit 1ns;
	timeprecision 1ps;

	import ovm_pkg::*;
	import mti_fli::*;
	import rsv_solyr_pkg::*;

	`include \"ovm_macros.svh\"
	`include \"rsv_defines.svh\"

[rsv_print_fpga $vf_ rec \n]
[rsv_print_fpga $vf_ ei \n]
[rsv_print_fpga $vf_ scb \n]

endpackage : usr_solyr_pkg

"
