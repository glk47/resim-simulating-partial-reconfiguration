set str "[rsv_print_license]
`timescale 1ns/1ps

module $nm_
(
[rsv_print_portmap $ri_ io ,\n]
);

	[lindex $my_module 0] [lindex $my_module 1] rm (
[rsv_print_portmap $ri_ inst ,\n \ ]
	);

endmodule


"
