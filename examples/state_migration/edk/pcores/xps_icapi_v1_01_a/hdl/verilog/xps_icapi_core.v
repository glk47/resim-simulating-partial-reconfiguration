//----------------------------------------------------------------------------
// xps_icapi_core.vhd - module
//----------------------------------------------------------------------------

`timescale 1 ns / 1 ns

module xps_icapi_core #(

	// -- DO NOT EDIT BELOW THIS LINE ------------------
	parameter C_SPLB_NATIVE_DWIDTH          = 128,
	parameter C_MPLB_NATIVE_DWIDTH          = 128,
	parameter C_FAMILY                      = "virtex5",
	// -- DO NOT EDIT ABOVE THIS LINE ------------------

	// -- ADD USER PARAMETERS BELOW THIS LINE ----------
	parameter C_MEM_BASEADDR                = 'hffffffff,
	parameter C_MEM_HIGHADDR                = 'h00000000,
	parameter C_RESIM                       = 1
	// -- ADD USER PARAMETERS ABOVE THIS LINE ----------

)
(
	// -- DO NOT EDIT BELOW THIS LINE ------------------
	input                                   Bus2IP_Clk,
	input                                   Bus2IP_Reset,
	input    [31:0]                         Bus2IP_Addr,
	input                                   Bus2IP_CS,
	input                                   Bus2IP_RNW,
	input    [C_SPLB_NATIVE_DWIDTH-1:0]     Bus2IP_Data,
	input    [C_SPLB_NATIVE_DWIDTH/8-1:0]   Bus2IP_BE,
	input                                   Bus2IP_Burst,
	input    [8:0]                          Bus2IP_BurstLength,
	input                                   Bus2IP_RdReq,
	input                                   Bus2IP_WrReq,
	output                                  IP2Bus_AddrAck,
	output   [C_SPLB_NATIVE_DWIDTH-1:0]     IP2Bus_Data,
	output                                  IP2Bus_RdAck,
	output                                  IP2Bus_WrAck,
	output                                  IP2Bus_Error,
	input                                   Bus2IP_Mst_Clk,
	input                                   Bus2IP_Mst_Reset,
	output                                  IP2Bus_MstRd_Req,
	output                                  IP2Bus_MstWr_Req,
	output   [31:0]                         IP2Bus_Mst_Addr,
	output   [C_MPLB_NATIVE_DWIDTH/8-1:0]   IP2Bus_Mst_BE,
	output   [11:0]                         IP2Bus_Mst_Length,
	output                                  IP2Bus_Mst_Type,
	output                                  IP2Bus_Mst_Lock,
	output                                  IP2Bus_Mst_Reset,
	input                                   Bus2IP_Mst_CmdAck,
	input                                   Bus2IP_Mst_Cmplt,
	input                                   Bus2IP_Mst_Error,
	input                                   Bus2IP_Mst_Rearbitrate,
	input                                   Bus2IP_Mst_Cmd_Timeout,
	input    [C_MPLB_NATIVE_DWIDTH-1:0]     Bus2IP_MstRd_d,
	input    [C_MPLB_NATIVE_DWIDTH/8-1:0]   Bus2IP_MstRd_rem,
	input                                   Bus2IP_MstRd_sof_n,
	input                                   Bus2IP_MstRd_eof_n,
	input                                   Bus2IP_MstRd_src_rdy_n,
	input                                   Bus2IP_MstRd_src_dsc_n,
	output                                  IP2Bus_MstRd_dst_rdy_n,
	output                                  IP2Bus_MstRd_dst_dsc_n,
	output   [C_MPLB_NATIVE_DWIDTH-1:0]     IP2Bus_MstWr_d,
	output   [C_MPLB_NATIVE_DWIDTH/8-1:0]   IP2Bus_MstWr_rem,
	output                                  IP2Bus_MstWr_sof_n,
	output                                  IP2Bus_MstWr_eof_n,
	output                                  IP2Bus_MstWr_src_rdy_n,
	output                                  IP2Bus_MstWr_src_dsc_n,
	input                                   Bus2IP_MstWr_dst_rdy_n,
	input                                   Bus2IP_MstWr_dst_dsc_n,
	// -- DO NOT EDIT ABOVE THIS LINE ------------------

	// -- ADD USER PORTS BELOW THIS LINE ---------------
	input                                   ICAP_Clk,
	output                                  IP2INTC_Irpt
	// -- ADD USER PORTS ABOVE THIS LINE ---------------

); // xps_icapi_core
	
	wire                                    rc_start;
	wire                                    rc_bop;
	wire     [31:0]                         rc_baddr;
	wire     [31:0]                         rc_bsize;
	wire                                    rc_done;
	
	wire                                    ma_req;
	wire                                    xbm_gnt;
	wire                                    ma_select;
	wire     [31:0]                         ma_addr;
	wire     [31:0]                         ma_data;
	wire                                    ma_rnw;
	wire     [3:0]                          ma_be;
	wire                                    xbm_ack;
	wire     [31:0]                         xbm_data;
	
	// ICAPI_REGS Instance
	// -------------------------------------------------
	
	icapi_regs #(
		.C_DWIDTH                   ( C_SPLB_NATIVE_DWIDTH   ),
		.C_MEM_BASEADDR             ( C_MEM_BASEADDR         ),
		.C_MEM_HIGHADDR             ( C_MEM_HIGHADDR         )
	) icapi_regs_0 (
		.Bus2IP_Clk                 ( Bus2IP_Clk             ),
		.Bus2IP_Reset               ( Bus2IP_Reset           ),
		.Bus2IP_Addr                ( Bus2IP_Addr            ),
		.Bus2IP_CS                  ( Bus2IP_CS              ),
		.Bus2IP_RNW                 ( Bus2IP_RNW             ),
		.Bus2IP_Data                ( Bus2IP_Data            ),
		.Bus2IP_BE                  ( Bus2IP_BE              ),
		.Bus2IP_Burst               ( Bus2IP_Burst           ),
		.Bus2IP_BurstLength         ( Bus2IP_BurstLength     ),
		.Bus2IP_RdReq               ( Bus2IP_RdReq           ),
		.Bus2IP_WrReq               ( Bus2IP_WrReq           ),
		.IP2Bus_AddrAck             ( IP2Bus_AddrAck         ),
		.IP2Bus_Data                ( IP2Bus_Data            ),
		.IP2Bus_RdAck               ( IP2Bus_RdAck           ),
		.IP2Bus_WrAck               ( IP2Bus_WrAck           ),
		.IP2Bus_Error               ( IP2Bus_Error           ),
		
		.rc_start                   ( rc_start               ),
		.rc_bop                     ( rc_bop                 ),
		.rc_baddr                   ( rc_baddr               ),
		.rc_bsize                   ( rc_bsize               ),
		.rc_done                    ( rc_done                ),
		
		.IP2INTC_Irpt               ( IP2INTC_Irpt           )
	);
	
	// ICAPI_MASTERIF Instance
	// -------------------------------------------------
	
	xbus_masterif #(
		.C_DWIDTH                   ( C_MPLB_NATIVE_DWIDTH   )
	) icapi_masterif_0 (
		.Bus2IP_Mst_Clk             ( Bus2IP_Mst_Clk         ),
		.Bus2IP_Mst_Reset           ( Bus2IP_Mst_Reset       ),
		.IP2Bus_MstRd_Req           ( IP2Bus_MstRd_Req       ),
		.IP2Bus_MstWr_Req           ( IP2Bus_MstWr_Req       ),
		.IP2Bus_Mst_Addr            ( IP2Bus_Mst_Addr        ),
		.IP2Bus_Mst_Length          ( IP2Bus_Mst_Length      ),
		.IP2Bus_Mst_BE              ( IP2Bus_Mst_BE          ),
		.IP2Bus_Mst_Type            ( IP2Bus_Mst_Type        ),
		.IP2Bus_Mst_Lock            ( IP2Bus_Mst_Lock        ),
		.IP2Bus_Mst_Reset           ( IP2Bus_Mst_Reset       ),
		.Bus2IP_Mst_CmdAck          ( Bus2IP_Mst_CmdAck      ),
		.Bus2IP_Mst_Cmplt           ( Bus2IP_Mst_Cmplt       ),
		.Bus2IP_Mst_Error           ( Bus2IP_Mst_Error       ),
		.Bus2IP_Mst_Rearbitrate     ( Bus2IP_Mst_Rearbitrate ),
		.Bus2IP_Mst_Cmd_Timeout     ( Bus2IP_Mst_Cmd_Timeout ),
		.Bus2IP_MstRd_d             ( Bus2IP_MstRd_d         ),
		.Bus2IP_MstRd_rem           ( Bus2IP_MstRd_rem       ),
		.Bus2IP_MstRd_sof_n         ( Bus2IP_MstRd_sof_n     ),
		.Bus2IP_MstRd_eof_n         ( Bus2IP_MstRd_eof_n     ),
		.Bus2IP_MstRd_src_rdy_n     ( Bus2IP_MstRd_src_rdy_n ),
		.Bus2IP_MstRd_src_dsc_n     ( Bus2IP_MstRd_src_dsc_n ),
		.IP2Bus_MstRd_dst_rdy_n     ( IP2Bus_MstRd_dst_rdy_n ),
		.IP2Bus_MstRd_dst_dsc_n     ( IP2Bus_MstRd_dst_dsc_n ),
		.IP2Bus_MstWr_d             ( IP2Bus_MstWr_d         ),
		.IP2Bus_MstWr_rem           ( IP2Bus_MstWr_rem       ),
		.IP2Bus_MstWr_sof_n         ( IP2Bus_MstWr_sof_n     ),
		.IP2Bus_MstWr_eof_n         ( IP2Bus_MstWr_eof_n     ),
		.IP2Bus_MstWr_src_rdy_n     ( IP2Bus_MstWr_src_rdy_n ),
		.IP2Bus_MstWr_src_dsc_n     ( IP2Bus_MstWr_src_dsc_n ),
		.Bus2IP_MstWr_dst_rdy_n     ( Bus2IP_MstWr_dst_rdy_n ),
		.Bus2IP_MstWr_dst_dsc_n     ( Bus2IP_MstWr_dst_dsc_n ),
		
		.ma_req                     ( ma_req                 ),
		.xbm_gnt                    ( xbm_gnt                ),
		.ma_select                  ( ma_select              ),
		.ma_addr                    ( ma_addr                ),
		.ma_data                    ( ma_data                ),
		.ma_rnw                     ( ma_rnw                 ),
		.ma_be                      ( ma_be                  ),
		.xbm_ack                    ( xbm_ack                ),
		.xbm_data                   ( xbm_data               )
	);

	// ICAPI Instance
	// -------------------------------------------------
	
	icapi #(
		.C_DWIDTH                   ( 32                     ),
		.C_RESIM                    ( C_RESIM                ),
		.C_FAMILY                   ( C_FAMILY               )
	) icapi_0 (
		.clk                        ( ICAP_Clk               ), // TODO: cross-clock domain
		.rstn                       ( ~Bus2IP_Reset          ), // TODO: low-active reset
		.rc_start                   ( rc_start               ),
		.rc_bop                     ( rc_bop                 ),
		.rc_baddr                   ( rc_baddr               ),
		.rc_bsize                   ( rc_bsize               ),
		.rc_done                    ( rc_done                ),
		.ma_req                     ( ma_req                 ),
		.xbm_gnt                    ( xbm_gnt                ),
		.ma_select                  ( ma_select              ),
		.ma_addr                    ( ma_addr                ),
		.ma_data                    ( ma_data                ),
		.ma_rnw                     ( ma_rnw                 ),
		.ma_be                      ( ma_be                  ),
		.xbm_ack                    ( xbm_ack                ),
		.xbm_data                   ( xbm_data               )
	);

endmodule
