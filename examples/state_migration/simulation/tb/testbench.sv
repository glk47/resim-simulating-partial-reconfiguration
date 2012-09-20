/*******************************************************************

 *******************************************************************/

`timescale 1ns / 1ps

module board
(

);

  reg                sys_clk   = 0; // lingkang: clock & reset for plb/ppc
  reg                sys_reset = 0; // lingkang: clock & reset for plb/ppc

  wire               uart_0_rx;
  wire               uart_0_tx;

  wire [0:1]         ddr2_sdram_ODT;
  wire [0:12]        ddr2_sdram_A;
  wire [0:1]         ddr2_sdram_BA;
  wire               ddr2_sdram_CAS_N;
  wire               ddr2_sdram_CKE;
  wire               ddr2_sdram_CS_N;
  wire               ddr2_sdram_RAS_N;
  wire               ddr2_sdram_WE_N;
  wire [1:0]         ddr2_sdram_CK;
  wire [1:0]         ddr2_sdram_CK_N;
  wire [0:7]         ddr2_sdram_DM;
  wire [0:7]         ddr2_sdram_DQS;
  wire [0:7]         ddr2_sdram_DQS_N;
  wire [0:63]        ddr2_sdram_DQ;

  wire               net_gnd_1bit;
  wire               net_vcc_1bit;
  wire [1:0]         net_gnd_2bit; // must use wires for inout ports
  wire [1:0]         net_vcc_2bit; // must use wires for inout ports
  
`ifdef SYSTEM_IMPLEMENTATION 
  defparam system.ddr2_sdram_0.ddr2_sdram_0.C_SIM_ONLY = 1; // = 1 skip the 200 us wait time at startup
  defparam ddr2_0.MEM_BITS = 18; // for simulation, only use 16MB memory
  defparam ddr2_1.MEM_BITS = 18; // 18bit = 256K, each storage = 64byte (one burst length)
  defparam ddr2_2.MEM_BITS = 18; //
  defparam ddr2_3.MEM_BITS = 18; //
`endif

//-------------------------------------------------------------------
// DUT: system
//-------------------------------------------------------------------

  system
    system (
      .fpga_0_sys_clk_pin                  ( sys_clk             ),
      .fpga_0_sys_rst_pin                  ( sys_reset           ),
      
`ifdef SYSTEM_IMPLEMENTATION 
      .fpga_0_ddr2_sdram_ODT_pin           ( ddr2_sdram_ODT      ),
      .fpga_0_ddr2_sdram_A_pin             ( ddr2_sdram_A        ),
      .fpga_0_ddr2_sdram_BA_pin            ( ddr2_sdram_BA       ),
      .fpga_0_ddr2_sdram_CAS_N_pin         ( ddr2_sdram_CAS_N    ),
      .fpga_0_ddr2_sdram_CKE_pin           ( ddr2_sdram_CKE      ),
      .fpga_0_ddr2_sdram_CS_N_pin          ( ddr2_sdram_CS_N     ),
      .fpga_0_ddr2_sdram_RAS_N_pin         ( ddr2_sdram_RAS_N    ),
      .fpga_0_ddr2_sdram_WE_N_pin          ( ddr2_sdram_WE_N     ),
      .fpga_0_ddr2_sdram_CK_pin            ( ddr2_sdram_CK       ),
      .fpga_0_ddr2_sdram_CK_N_pin          ( ddr2_sdram_CK_N     ),
      .fpga_0_ddr2_sdram_DM_pin            ( ddr2_sdram_DM       ),
      .fpga_0_ddr2_sdram_DQS_pin           ( ddr2_sdram_DQS      ),
      .fpga_0_ddr2_sdram_DQS_N_pin         ( ddr2_sdram_DQS_N    ),
      .fpga_0_ddr2_sdram_DQ_pin            ( ddr2_sdram_DQ       ),
`endif
      
`ifdef SYSTEM_IMPLEMENTATION 
      .fpga_0_SysACE_MPA_pin               ( /* not-connected */ ),
      .fpga_0_SysACE_CLK_pin               ( /* not-connected */ ),
      .fpga_0_SysACE_MPIRQ_pin             ( /* not-connected */ ),
      .fpga_0_SysACE_CEN_pin               ( /* not-connected */ ),
      .fpga_0_SysACE_OEN_pin               ( /* not-connected */ ),
      .fpga_0_SysACE_WEN_pin               ( /* not-connected */ ),
      .fpga_0_SysACE_MPD_pin               ( /* not-connected */ ),
`endif

      .fpga_0_RS232_Uart_0_RX_pin          ( uart_0_rx           ),
      .fpga_0_RS232_Uart_0_TX_pin          ( uart_0_tx           )
    );

  always #5 sys_clk = ~sys_clk; // lingkang: clock_in_pin is 100MHz, see MHS file
  
  initial begin
    $timeformat(-9,3,"ns", 5);
  
    sys_reset = 0;
    #1_000;
    sys_reset = 1;
  
  end

//-------------------------------------------------------------------
// UART
//-------------------------------------------------------------------

  uart_monitor
    #(
      .C_UART_ID(0),
      .C_CLK_FREQ_HZ(100000000),
`ifdef SYSTEM_IMPLEMENTATION 
      .C_BAUDRATE(115200),
`else
      .C_BAUDRATE(1000000),
`endif
      .C_DATA_BITS(8),
      .C_USE_PARITY(0),
      .C_ODD_PARITY(0)
    )
    uart_monitor_0
      (
        .clk(system.clk_100MHz_PLL0_ADJUST),
        .rstn(sys_reset),
        .rx(uart_0_tx),
        .tx(uart_0_rx)
      );
  
//-------------------------------------------------------------------
// DDR2 memory
//-------------------------------------------------------------------

`ifdef SYSTEM_IMPLEMENTATION 
  ddr2
    ddr2_0
      (
        .ck      (ddr2_sdram_CK[0]),       // I
        .ck_n    (ddr2_sdram_CK_N[0]),     // I
        .cke     (ddr2_sdram_CKE),         // I
        .cs_n    (ddr2_sdram_CS_N),        // I
        .ras_n   (ddr2_sdram_RAS_N),       // I
        .cas_n   (ddr2_sdram_CAS_N),       // I
        .we_n    (ddr2_sdram_WE_N),        // I
        .dm_rdqs (ddr2_sdram_DM[0:1]),     // IO [1:0]
        .ba      (ddr2_sdram_BA),          // I
        .addr    (ddr2_sdram_A),           // I  [13:0]
        .dq      (ddr2_sdram_DQ[0:15]),    // IO [15:0]
        .dqs     (ddr2_sdram_DQS[0:1]),    // IO [1:0]
        .dqs_n   (ddr2_sdram_DQS_N[0:1]),  // IO [1:0]
        .rdqs_n  (net_gnd_2bit),           // O [1:0]
        .odt     (ddr2_sdram_ODT[0])       // I
      );

  ddr2
    ddr2_1
      (
        .ck      (ddr2_sdram_CK[0]),       // I
        .ck_n    (ddr2_sdram_CK_N[0]),     // I
        .cke     (ddr2_sdram_CKE),         // I
        .cs_n    (ddr2_sdram_CS_N),        // I
        .ras_n   (ddr2_sdram_RAS_N),       // I
        .cas_n   (ddr2_sdram_CAS_N),       // I
        .we_n    (ddr2_sdram_WE_N),        // I
        .dm_rdqs (ddr2_sdram_DM[2:3]),     // IO [1:0]
        .ba      (ddr2_sdram_BA),          // I
        .addr    (ddr2_sdram_A),           // I  [13:0]
        .dq      (ddr2_sdram_DQ[16:31]),   // IO [15:0]
        .dqs     (ddr2_sdram_DQS[2:3]),    // IO [1:0]
        .dqs_n   (ddr2_sdram_DQS_N[2:3]),  // IO [1:0]
        .rdqs_n  (net_gnd_2bit),           // O [1:0]
        .odt     (ddr2_sdram_ODT[0])       // I
      );

  ddr2
    ddr2_2
      (
        .ck      (ddr2_sdram_CK[1]),       // I
        .ck_n    (ddr2_sdram_CK_N[1]),     // I
        .cke     (ddr2_sdram_CKE),         // I
        .cs_n    (ddr2_sdram_CS_N),        // I
        .ras_n   (ddr2_sdram_RAS_N),       // I
        .cas_n   (ddr2_sdram_CAS_N),       // I
        .we_n    (ddr2_sdram_WE_N),        // I
        .dm_rdqs (ddr2_sdram_DM[4:5]),     // IO [1:0]
        .ba      (ddr2_sdram_BA),          // I
        .addr    (ddr2_sdram_A),           // I  [13:0]
        .dq      (ddr2_sdram_DQ[32:47]),   // IO [15:0]
        .dqs     (ddr2_sdram_DQS[4:5]),    // IO [1:0]
        .dqs_n   (ddr2_sdram_DQS_N[4:5]),  // IO [1:0]
        .rdqs_n  (net_gnd_2bit),           // O [1:0]
        .odt     (ddr2_sdram_ODT[1])       // I
      );

  ddr2
    ddr2_3
      (
        .ck      (ddr2_sdram_CK[1]),       // I
        .ck_n    (ddr2_sdram_CK_N[1]),     // I
        .cke     (ddr2_sdram_CKE),         // I
        .cs_n    (ddr2_sdram_CS_N),        // I
        .ras_n   (ddr2_sdram_RAS_N),       // I
        .cas_n   (ddr2_sdram_CAS_N),       // I
        .we_n    (ddr2_sdram_WE_N),        // I
        .dm_rdqs (ddr2_sdram_DM[6:7]),     // IO [1:0]
        .ba      (ddr2_sdram_BA),          // I
        .addr    (ddr2_sdram_A),           // I  [13:0]
        .dq      (ddr2_sdram_DQ[48:63]),   // IO [15:0]
        .dqs     (ddr2_sdram_DQS[6:7]),    // IO [1:0]
        .dqs_n   (ddr2_sdram_DQS_N[6:7]),  // IO [1:0]
        .rdqs_n  (net_gnd_2bit),           // O [1:0]
        .odt     (ddr2_sdram_ODT[1])       // I
      );
`endif

  assign net_gnd_1bit = 1'b0;
  assign net_vcc_1bit = 1'b1;
  assign net_gnd_2bit = 2'b00;
  assign net_vcc_2bit = 2'b11;
  
//-------------------------------------------------------------------
// ReSim Sim-only-Layer Instance
//-------------------------------------------------------------------

  my_solyr i_sol(); 

endmodule /* testbench */
