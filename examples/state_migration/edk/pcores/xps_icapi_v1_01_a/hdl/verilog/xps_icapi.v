//----------------------------------------------------------------------------
// xps_icapi.vhd - module
//----------------------------------------------------------------------------

`timescale 1 ns / 1 ns
`uselib lib=simmodels_v1_00_a lib=xps_icapi_v1_01_a lib=ipif_v1_00_a lib=plbv46_master_burst_v1_01_a lib=plbv46_slave_burst_v1_01_a

module xps_icapi #(
	
	// -- DO NOT EDIT BELOW THIS LINE ------------------
	parameter C_SPLB_AWIDTH                = 32,
	parameter C_SPLB_DWIDTH                = 128,
	parameter C_SPLB_NUM_MASTERS           = 8,
	parameter C_SPLB_MID_WIDTH             = 3,
	parameter C_SPLB_NATIVE_DWIDTH         = 128,
	parameter C_SPLB_P2P                   = 0,
	parameter C_SPLB_SUPPORT_BURSTS        = 1,
	parameter C_SPLB_SMALLEST_MASTER       = 32,
	parameter C_SPLB_CLK_PERIOD_PS         = 10000,
	parameter C_INCLUDE_DPHASE_TIMER        = 1,
	parameter C_FAMILY                      = "virtex5",
	parameter C_MPLB_AWIDTH                 = 32,
	parameter C_MPLB_DWIDTH                 = 128,
	parameter C_MPLB_NATIVE_DWIDTH          = 128,
	parameter C_MPLB_P2P                    = 0,
	parameter C_MPLB_SMALLEST_SLAVE         = 32,
	parameter C_MPLB_CLK_PERIOD_PS          = 10000,
	// -- DO NOT EDIT ABOVE THIS LINE ------------------

	// -- ADD USER PARAMETERS BELOW THIS LINE ----------
	parameter C_MEM_BASEADDR                = 'hffffffff,
	parameter C_MEM_HIGHADDR                = 'h00000000,
	parameter C_RESIM                       = 1
	// -- ADD USER PARAMETERS ABOVE THIS LINE ----------
	
)
(
	// -- DO NOT EDIT BELOW THIS LINE ------------------
	input                                   SPLB_Clk,
	input                                   SPLB_Rst,
	input        [0:C_SPLB_AWIDTH-1]        PLB_ABus,
	input        [0:C_SPLB_AWIDTH-1]        PLB_UABus,
	input                                   PLB_PAValid,
	input                                   PLB_SAValid,
	input                                   PLB_rdPrim,
	input                                   PLB_wrPrim,
	input        [0:C_SPLB_MID_WIDTH-1]     PLB_masterID,
	input                                   PLB_abort,
	input                                   PLB_busLock,
	input                                   PLB_RNW,
	input        [0:C_SPLB_DWIDTH/8-1]      PLB_BE,
	input        [0:1]                      PLB_MSize,
	input        [0:3]                      PLB_size,
	input        [0:2]                      PLB_type,
	input                                   PLB_lockErr,
	input        [0:C_SPLB_DWIDTH-1]        PLB_wrDBus,
	input                                   PLB_wrBurst,
	input                                   PLB_rdBurst,
	input                                   PLB_wrPendReq,
	input                                   PLB_rdPendReq,
	input        [0:1]                      PLB_wrPendPri,
	input        [0:1]                      PLB_rdPendPri,
	input        [0:1]                      PLB_reqPri,
	input        [0:15]                     PLB_TAttribute,
	output                                  Sl_addrAck,
	output       [0:1]                      Sl_SSize,
	output                                  Sl_wait,
	output                                  Sl_rearbitrate,
	output                                  Sl_wrDAck,
	output                                  Sl_wrComp,
	output                                  Sl_wrBTerm,
	output       [0:C_SPLB_DWIDTH-1]        Sl_rdDBus,
	output       [0:3]                      Sl_rdWdAddr,
	output                                  Sl_rdDAck,
	output                                  Sl_rdComp,
	output                                  Sl_rdBTerm,
	output       [0:C_SPLB_NUM_MASTERS-1]   Sl_MBusy,
	output       [0:C_SPLB_NUM_MASTERS-1]   Sl_MWrErr,
	output       [0:C_SPLB_NUM_MASTERS-1]   Sl_MRdErr,
	output       [0:C_SPLB_NUM_MASTERS-1]   Sl_MIRQ,
	
	input                                   MPLB_Clk,
	input                                   MPLB_Rst,
	output                                  MD_error,
	output                                  M_request,
	output       [0:1]                      M_priority,
	output                                  M_busLock,
	output                                  M_RNW,
	output       [0:C_MPLB_DWIDTH/8-1]      M_BE,
	output       [0:1]                      M_MSize,
	output       [0:3]                      M_size,
	output       [0:2]                      M_type,
	output       [0:15]                     M_TAttribute,
	output                                  M_lockErr,
	output                                  M_abort,
	output       [0:C_MPLB_AWIDTH-1]        M_UABus,
	output       [0:C_MPLB_AWIDTH-1]        M_ABus,
	output       [0:C_MPLB_DWIDTH-1]        M_wrDBus,
	output                                  M_wrBurst,
	output                                  M_rdBurst,
	input                                   PLB_MAddrAck,
	input        [0:1]                      PLB_MSSize,
	input                                   PLB_MRearbitrate,
	input                                   PLB_MTimeout,
	input                                   PLB_MBusy,
	input                                   PLB_MRdErr,
	input                                   PLB_MWrErr,
	input                                   PLB_MIRQ,
	input        [0:C_MPLB_DWIDTH-1]        PLB_MRdDBus,
	input        [0:3]                      PLB_MRdWdAddr,
	input                                   PLB_MRdDAck,
	input                                   PLB_MRdBTerm,
	input                                   PLB_MWrDAck,
	input                                   PLB_MWrBTerm,
	// -- DO NOT EDIT ABOVE THIS LINE ------------------

	// -- ADD USER PORTS BELOW THIS LINE ---------------
	input                                   ICAP_Clk,
	output                                  IP2INTC_Irpt
	// -- ADD USER PORTS ABOVE THIS LINE ---------------

); // xps_icapi

	wire                                    Bus2IP_Clk;
	wire                                    Bus2IP_Reset;
	wire   [0 : 32-1]                       Bus2IP_Addr;
	wire                                    Bus2IP_CS;
	wire                                    Bus2IP_RNW;
	wire   [0 : 128-1]                      Bus2IP_Data;
	wire   [0 : 128/8-1]                    Bus2IP_BE;
	wire                                    Bus2IP_Burst;
	wire   [0 : 8]                          Bus2IP_BurstLength;
	wire                                    Bus2IP_RdReq;
	wire                                    Bus2IP_WrReq;
	wire                                    IP2Bus_AddrAck;
	wire   [0 : 128-1]                      IP2Bus_Data;
	wire                                    IP2Bus_RdAck;
	wire                                    IP2Bus_WrAck;
	wire                                    IP2Bus_Error;
	
	wire                                    Bus2IP_Mst_Clk;
	wire                                    Bus2IP_Mst_Reset;
	wire                                    IP2Bus_MstRd_Req;
	wire                                    IP2Bus_MstWr_Req;
	wire   [0:32-1]                         IP2Bus_Mst_Addr;
	wire   [0:11]                           IP2Bus_Mst_Length;
	wire   [0:128/8-1]                      IP2Bus_Mst_BE;
	wire                                    IP2Bus_Mst_Type;
	wire                                    IP2Bus_Mst_Lock;
	wire                                    IP2Bus_Mst_Reset;
	wire                                    Bus2IP_Mst_CmdAck;
	wire                                    Bus2IP_Mst_Cmplt;
	wire                                    Bus2IP_Mst_Error;
	wire                                    Bus2IP_Mst_Rearbitrate;
	wire                                    Bus2IP_Mst_Cmd_Timeout;
	wire   [0:128-1]                        Bus2IP_MstRd_d;
	wire   [0:128/8-1]                      Bus2IP_MstRd_rem;
	wire                                    Bus2IP_MstRd_sof_n;
	wire                                    Bus2IP_MstRd_eof_n;
	wire                                    Bus2IP_MstRd_src_rdy_n;
	wire                                    Bus2IP_MstRd_src_dsc_n;
	wire                                    IP2Bus_MstRd_dst_rdy_n;
	wire                                    IP2Bus_MstRd_dst_dsc_n;
	wire   [0:128-1]                        IP2Bus_MstWr_d;
	wire   [0:128/8-1]                      IP2Bus_MstWr_rem;
	wire                                    IP2Bus_MstWr_sof_n;
	wire                                    IP2Bus_MstWr_eof_n;
	wire                                    IP2Bus_MstWr_src_rdy_n;
	wire                                    IP2Bus_MstWr_src_dsc_n;
	wire                                    Bus2IP_MstWr_dst_rdy_n;
	wire                                    Bus2IP_MstWr_dst_dsc_n;
	
	// Slave IPIF Instance
	// -------------------------------------------------

	plbv46_slave_burst_wrapper #(
		.C_SPLB_AWIDTH              ( C_SPLB_AWIDTH          ),
		.C_SPLB_DWIDTH              ( C_SPLB_DWIDTH          ),
		.C_SPLB_NUM_MASTERS         ( C_SPLB_NUM_MASTERS     ),
		.C_SPLB_MID_WIDTH           ( C_SPLB_MID_WIDTH       ),
		.C_SPLB_NATIVE_DWIDTH       ( C_SPLB_NATIVE_DWIDTH   ),
		.C_SPLB_P2P                 ( C_SPLB_P2P             ),
		.C_SPLB_SUPPORT_BURSTS      ( C_SPLB_SUPPORT_BURSTS  ),
		.C_SPLB_SMALLEST_MASTER     ( C_SPLB_SMALLEST_MASTER ),
		.C_SPLB_CLK_PERIOD_PS       ( C_SPLB_CLK_PERIOD_PS   ),
		.C_FAMILY                   ( C_FAMILY               ),
		.C_MEM_BASEADDR             ( C_MEM_BASEADDR         ),
		.C_MEM_HIGHADDR             ( C_MEM_HIGHADDR         )
	) PLBV46_SLAVE_BURST_I (
		.SPLB_Clk                   ( SPLB_Clk               ),
		.SPLB_Rst                   ( SPLB_Rst               ),
		.PLB_ABus                   ( PLB_ABus               ),
		.PLB_UABus                  ( PLB_UABus              ),
		.PLB_PAValid                ( PLB_PAValid            ),
		.PLB_SAValid                ( PLB_SAValid            ),
		.PLB_rdPrim                 ( PLB_rdPrim             ),
		.PLB_wrPrim                 ( PLB_wrPrim             ),
		.PLB_masterID               ( PLB_masterID           ),
		.PLB_abort                  ( PLB_abort              ),
		.PLB_busLock                ( PLB_busLock            ),
		.PLB_RNW                    ( PLB_RNW                ),
		.PLB_BE                     ( PLB_BE                 ),
		.PLB_MSize                  ( PLB_MSize              ),
		.PLB_size                   ( PLB_size               ),
		.PLB_type                   ( PLB_type               ),
		.PLB_lockErr                ( PLB_lockErr            ),
		.PLB_wrDBus                 ( PLB_wrDBus             ),
		.PLB_wrBurst                ( PLB_wrBurst            ),
		.PLB_rdBurst                ( PLB_rdBurst            ),
		.PLB_wrPendReq              ( PLB_wrPendReq          ),
		.PLB_rdPendReq              ( PLB_rdPendReq          ),
		.PLB_wrPendPri              ( PLB_wrPendPri          ),
		.PLB_rdPendPri              ( PLB_rdPendPri          ),
		.PLB_reqPri                 ( PLB_reqPri             ),
		.PLB_TAttribute             ( PLB_TAttribute         ),
		.Sl_addrAck                 ( Sl_addrAck             ),
		.Sl_SSize                   ( Sl_SSize               ),
		.Sl_wait                    ( Sl_wait                ),
		.Sl_rearbitrate             ( Sl_rearbitrate         ),
		.Sl_wrDAck                  ( Sl_wrDAck              ),
		.Sl_wrComp                  ( Sl_wrComp              ),
		.Sl_wrBTerm                 ( Sl_wrBTerm             ),
		.Sl_rdDBus                  ( Sl_rdDBus              ),
		.Sl_rdWdAddr                ( Sl_rdWdAddr            ),
		.Sl_rdDAck                  ( Sl_rdDAck              ),
		.Sl_rdComp                  ( Sl_rdComp              ),
		.Sl_rdBTerm                 ( Sl_rdBTerm             ),
		.Sl_MBusy                   ( Sl_MBusy               ),
		.Sl_MWrErr                  ( Sl_MWrErr              ),
		.Sl_MRdErr                  ( Sl_MRdErr              ),
		.Sl_MIRQ                    ( Sl_MIRQ                ),
		.Bus2IP_Clk                 ( Bus2IP_Clk             ),
		.Bus2IP_Reset               ( Bus2IP_Reset           ),
		.IP2Bus_Data                ( IP2Bus_Data            ),
		.IP2Bus_WrAck               ( IP2Bus_WrAck           ),
		.IP2Bus_RdAck               ( IP2Bus_RdAck           ),
		.IP2Bus_AddrAck             ( IP2Bus_AddrAck         ),
		.IP2Bus_Error               ( IP2Bus_Error           ),
		.Bus2IP_Addr                ( Bus2IP_Addr            ),
		.Bus2IP_Data                ( Bus2IP_Data            ),
		.Bus2IP_RNW                 ( Bus2IP_RNW             ),
		.Bus2IP_BE                  ( Bus2IP_BE              ),
		.Bus2IP_Burst               ( Bus2IP_Burst           ),
		.Bus2IP_BurstLength         ( Bus2IP_BurstLength     ),
		.Bus2IP_WrReq               ( Bus2IP_WrReq           ),
		.Bus2IP_RdReq               ( Bus2IP_RdReq           ),
		.Bus2IP_CS                  ( Bus2IP_CS              )
	);
	
	// Master IPIF Instance
	// -------------------------------------------------
	
	plbv46_master_burst_wrapper #(
		.C_MPLB_AWIDTH              ( C_MPLB_AWIDTH          ),
		.C_MPLB_DWIDTH              ( C_MPLB_DWIDTH          ),
		.C_MPLB_NATIVE_DWIDTH       ( C_MPLB_NATIVE_DWIDTH   ),
		.C_MPLB_SMALLEST_SLAVE      ( C_MPLB_SMALLEST_SLAVE  ),
		.C_INHIBIT_CC_BLE_INCLUSION ( 0                      ),
		.C_FAMILY                   ( C_FAMILY               )
	) PLBV46_MASTER_BURST_I (
		.MPLB_Clk                   ( MPLB_Clk               ),
		.MPLB_Rst                   ( MPLB_Rst               ),
		.MD_error                   ( MD_error               ),
		.M_request                  ( M_request              ),
		.M_priority                 ( M_priority             ),
		.M_busLock                  ( M_busLock              ),
		.M_RNW                      ( M_RNW                  ),
		.M_BE                       ( M_BE                   ),
		.M_MSize                    ( M_MSize                ),
		.M_size                     ( M_size                 ),
		.M_type                     ( M_type                 ),
		.M_TAttribute               ( M_TAttribute           ),
		.M_lockErr                  ( M_lockErr              ),
		.M_abort                    ( M_abort                ),
		.M_UABus                    ( M_UABus                ),
		.M_ABus                     ( M_ABus                 ),
		.M_wrDBus                   ( M_wrDBus               ),
		.M_wrBurst                  ( M_wrBurst              ),
		.M_rdBurst                  ( M_rdBurst              ),
		.PLB_MAddrAck               ( PLB_MAddrAck           ),
		.PLB_MSSize                 ( PLB_MSSize             ),
		.PLB_MRearbitrate           ( PLB_MRearbitrate       ),
		.PLB_MTimeout               ( PLB_MTimeout           ),
		.PLB_MBusy                  ( PLB_MBusy              ),
		.PLB_MRdErr                 ( PLB_MRdErr             ),
		.PLB_MWrErr                 ( PLB_MWrErr             ),
		.PLB_MIRQ                   ( PLB_MIRQ               ),
		.PLB_MRdDBus                ( PLB_MRdDBus            ),
		.PLB_MRdWdAddr              ( PLB_MRdWdAddr          ),
		.PLB_MRdDAck                ( PLB_MRdDAck            ),
		.PLB_MRdBTerm               ( PLB_MRdBTerm           ),
		.PLB_MWrDAck                ( PLB_MWrDAck            ),
		.PLB_MWrBTerm               ( PLB_MWrBTerm           ),
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
		.Bus2IP_MstWr_dst_dsc_n     ( Bus2IP_MstWr_dst_dsc_n )
	);
	
	// XPS_ICAPI_CORE Instance
	// -------------------------------------------------
	
	xps_icapi_core #(
		.C_SPLB_NATIVE_DWIDTH       ( C_SPLB_NATIVE_DWIDTH   ),
		.C_MPLB_NATIVE_DWIDTH       ( C_MPLB_NATIVE_DWIDTH   ),
		.C_MEM_BASEADDR             ( C_MEM_BASEADDR         ),
		.C_MEM_HIGHADDR             ( C_MEM_HIGHADDR         ),
		.C_FAMILY                   ( C_FAMILY               ),
		.C_RESIM                    ( C_RESIM                )
	) user_logic_i (
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
		.ICAP_Clk                   ( ICAP_Clk               ),
		.IP2INTC_Irpt               ( IP2INTC_Irpt           )
	);

endmodule
