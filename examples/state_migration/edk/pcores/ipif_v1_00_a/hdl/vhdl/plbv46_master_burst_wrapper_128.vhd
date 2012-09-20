------------------------------------------------------------------------------
-- plbv46_master_burst_wrapper.vhd - entity/architecture pair
------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

library proc_common_v3_00_a;
use proc_common_v3_00_a.proc_common_pkg.all;
use proc_common_v3_00_a.ipif_pkg.all;

library plbv46_master_burst_v1_01_a;
use plbv46_master_burst_v1_01_a.plbv46_master_burst;

------------------------------------------------------------------------------
-- Entity section
------------------------------------------------------------------------------
-- Definition of Generics:
--   C_SPLB_AWIDTH                -- PLBv46 slave: address bus width
--   C_SPLB_DWIDTH                -- PLBv46 slave: data bus width
--   C_SPLB_NUM_MASTERS           -- PLBv46 slave: Number of masters
--   C_SPLB_MID_WIDTH             -- PLBv46 slave: master ID bus width
--   C_SPLB_NATIVE_DWIDTH         -- PLBv46 slave: internal native data bus width
--   C_SPLB_P2P                   -- PLBv46 slave: point to point interconnect scheme
--   C_SPLB_SUPPORT_BURSTS        -- PLBv46 slave: support bursts
--   C_SPLB_SMALLEST_MASTER       -- PLBv46 slave: width of the smallest master
--   C_SPLB_CLK_PERIOD_PS         -- PLBv46 slave: bus clock in picoseconds
--   C_INCLUDE_DPHASE_TIMER       -- PLBv46 slave: Data Phase Timer configuration; 0 = exclude timer, 1 = include timer
--   C_FAMILY                     -- Xilinx FPGA family
--   C_MPLB_AWIDTH                -- PLBv46 master: address bus width
--   C_MPLB_DWIDTH                -- PLBv46 master: data bus width
--   C_MPLB_NATIVE_DWIDTH         -- PLBv46 master: internal native data width
--   C_MPLB_P2P                   -- PLBv46 master: point to point interconnect scheme
--   C_MPLB_SMALLEST_SLAVE        -- PLBv46 master: width of the smallest slave
--   C_MPLB_CLK_PERIOD_PS         -- PLBv46 master: bus clock in picoseconds
--
-- Definition of Ports:
--   SPLB_Clk                     -- PLB main bus clock
--   SPLB_Rst                     -- PLB main bus reset
--   PLB_ABus                     -- PLB address bus
--   PLB_UABus                    -- PLB upper address bus
--   PLB_PAValid                  -- PLB primary address valid indicator
--   PLB_SAValid                  -- PLB secondary address valid indicator
--   PLB_rdPrim                   -- PLB secondary to primary read request indicator
--   PLB_wrPrim                   -- PLB secondary to primary write request indicator
--   PLB_masterID                 -- PLB current master identifier
--   PLB_abort                    -- PLB abort request indicator
--   PLB_busLock                  -- PLB bus lock
--   PLB_RNW                      -- PLB read/not write
--   PLB_BE                       -- PLB byte enables
--   PLB_MSize                    -- PLB master data bus size
--   PLB_size                     -- PLB transfer size
--   PLB_type                     -- PLB transfer type
--   PLB_lockErr                  -- PLB lock error indicator
--   PLB_wrDBus                   -- PLB write data bus
--   PLB_wrBurst                  -- PLB burst write transfer indicator
--   PLB_rdBurst                  -- PLB burst read transfer indicator
--   PLB_wrPendReq                -- PLB write pending bus request indicator
--   PLB_rdPendReq                -- PLB read pending bus request indicator
--   PLB_wrPendPri                -- PLB write pending request priority
--   PLB_rdPendPri                -- PLB read pending request priority
--   PLB_reqPri                   -- PLB current request priority
--   PLB_TAttribute               -- PLB transfer attribute
--   Sl_addrAck                   -- Slave address acknowledge
--   Sl_SSize                     -- Slave data bus size
--   Sl_wait                      -- Slave wait indicator
--   Sl_rearbitrate               -- Slave re-arbitrate bus indicator
--   Sl_wrDAck                    -- Slave write data acknowledge
--   Sl_wrComp                    -- Slave write transfer complete indicator
--   Sl_wrBTerm                   -- Slave terminate write burst transfer
--   Sl_rdDBus                    -- Slave read data bus
--   Sl_rdWdAddr                  -- Slave read word address
--   Sl_rdDAck                    -- Slave read data acknowledge
--   Sl_rdComp                    -- Slave read transfer complete indicator
--   Sl_rdBTerm                   -- Slave terminate read burst transfer
--   Sl_MBusy                     -- Slave busy indicator
--   Sl_MWrErr                    -- Slave write error indicator
--   Sl_MRdErr                    -- Slave read error indicator
--   Sl_MIRQ                      -- Slave interrupt indicator
--   MPLB_Clk                     -- PLB main bus Clock
--   MPLB_Rst                     -- PLB main bus Reset
--   MD_error                     -- Master detected error status output
--   M_request                    -- Master request
--   M_priority                   -- Master request priority
--   M_busLock                    -- Master buslock
--   M_RNW                        -- Master read/nor write
--   M_BE                         -- Master byte enables
--   M_MSize                      -- Master data bus size
--   M_size                       -- Master transfer size
--   M_type                       -- Master transfer type
--   M_TAttribute                 -- Master transfer attribute
--   M_lockErr                    -- Master lock error indicator
--   M_abort                      -- Master abort bus request indicator
--   M_UABus                      -- Master upper address bus
--   M_ABus                       -- Master address bus
--   M_wrDBus                     -- Master write data bus
--   M_wrBurst                    -- Master burst write transfer indicator
--   M_rdBurst                    -- Master burst read transfer indicator
--   PLB_MAddrAck                 -- PLB reply to master for address acknowledge
--   PLB_MSSize                   -- PLB reply to master for slave data bus size
--   PLB_MRearbitrate             -- PLB reply to master for bus re-arbitrate indicator
--   PLB_MTimeout                 -- PLB reply to master for bus time out indicator
--   PLB_MBusy                    -- PLB reply to master for slave busy indicator
--   PLB_MRdErr                   -- PLB reply to master for slave read error indicator
--   PLB_MWrErr                   -- PLB reply to master for slave write error indicator
--   PLB_MIRQ                     -- PLB reply to master for slave interrupt indicator
--   PLB_MRdDBus                  -- PLB reply to master for read data bus
--   PLB_MRdWdAddr                -- PLB reply to master for read word address
--   PLB_MRdDAck                  -- PLB reply to master for read data acknowledge
--   PLB_MRdBTerm                 -- PLB reply to master for terminate read burst indicator
--   PLB_MWrDAck                  -- PLB reply to master for write data acknowledge
--   PLB_MWrBTerm                 -- PLB reply to master for terminate write burst indicator
------------------------------------------------------------------------------

entity plbv46_master_burst_wrapper is
  generic
  (
    -- DO NOT EDIT BELOW THIS LINE ---------------------
    C_MPLB_AWIDTH                  : integer              := 32;
    C_MPLB_DWIDTH                  : integer              := 128;
    C_MPLB_NATIVE_DWIDTH           : integer              := 128;
    C_MPLB_SMALLEST_SLAVE          : integer              := 32;
    C_INHIBIT_CC_BLE_INCLUSION     : integer              := 0;
    C_FAMILY                       : string               := "virtex5"
    -- DO NOT EDIT ABOVE THIS LINE ---------------------
    
    -- ADD USER GENERICS BELOW THIS LINE ---------------
    -- ADD USER GENERICS ABOVE THIS LINE ---------------
  );
  port
  (
    -- DO NOT EDIT BELOW THIS LINE ---------------------
    MPLB_Clk                       : in std_logic ;
    MPLB_Rst                       : in std_logic ;
    MD_error                       : out std_logic;
    M_request                      : out std_logic;
    M_priority                     : out std_logic_vector(0 to 1);
    M_busLock                      : out std_logic;
    M_RNW                          : out std_logic;
    M_BE                           : out std_logic_vector(0 to (C_MPLB_DWIDTH/8) - 1);
    M_MSize                        : out std_logic_vector(0 to 1);
    M_size                         : out std_logic_vector(0 to 3);
    M_type                         : out std_logic_vector(0 to 2);
    M_TAttribute                   : out std_logic_vector(0 to 15);
    M_abort                        : out std_logic;
    M_lockErr                      : out std_logic;
    M_ABus                         : out std_logic_vector(0 to 31);
    M_UABus                        : out std_logic_vector(0 to 31);
    M_wrBurst                      : out std_logic;
    M_rdBurst                      : out std_logic;
    M_wrDBus                       : out std_logic_vector(0 to C_MPLB_DWIDTH-1);
    PLB_MAddrAck                   : in  std_logic;
    PLB_MSSize                     : in  std_logic_vector(0 to 1);
    PLB_MRearbitrate               : in  std_logic;
    PLB_MTimeout                   : in  std_logic;
    PLB_MBusy                      : in  std_logic;
    PLB_MRdErr                     : in  std_logic;
    PLB_MWrErr                     : in  std_logic;
    PLB_MIRQ                       : in  std_logic;
    PLB_MRdDBus                    : in  std_logic_vector(0 to C_MPLB_DWIDTH-1);
    PLB_MRdWdAddr                  : in  std_logic_vector(0 to 3);
    PLB_MRdDAck                    : in  std_logic;
    PLB_MRdBTerm                   : in  std_logic;
    PLB_MWrDAck                    : in  std_logic;
    PLB_MWrBTerm                   : in  std_logic;
    -- DO NOT EDIT ABOVE THIS LINE ---------------------

    -- ADD USER PORTS BELOW THIS LINE ------------------
    Bus2IP_Mst_Clk                 : out std_logic;
    Bus2IP_Mst_Reset               : out std_logic;
    IP2Bus_MstRd_Req               : in  std_logic;
    IP2Bus_MstWr_Req               : in  std_logic;
    IP2Bus_Mst_Addr                : in  std_logic_vector(0 to C_MPLB_AWIDTH-1);
    IP2Bus_Mst_Length              : in  std_logic_vector(0 to 11);
    IP2Bus_Mst_BE                  : in  std_logic_vector(0 to 128/8 -1);     
    IP2Bus_Mst_Type                : in  std_logic;
    IP2Bus_Mst_Lock                : in  std_logic;
    IP2Bus_Mst_Reset               : in  std_logic;
    Bus2IP_Mst_CmdAck              : out std_logic;
    Bus2IP_Mst_Cmplt               : out std_logic;
    Bus2IP_Mst_Error               : out std_logic;
    Bus2IP_Mst_Rearbitrate         : out std_logic;
    Bus2IP_Mst_Cmd_Timeout         : out std_logic;
    Bus2IP_MstRd_d                 : out std_logic_vector(0 to 128-1); 
    Bus2IP_MstRd_rem               : out std_logic_vector(0 to 128/8-1); 
    Bus2IP_MstRd_sof_n             : out std_logic;
    Bus2IP_MstRd_eof_n             : out std_logic;
    Bus2IP_MstRd_src_rdy_n         : out std_logic;
    Bus2IP_MstRd_src_dsc_n         : out std_logic;
    IP2Bus_MstRd_dst_rdy_n         : in  std_logic;
    IP2Bus_MstRd_dst_dsc_n         : in  std_logic;
    IP2Bus_MstWr_d                 : in  std_logic_vector(0 to 128-1); 
    IP2Bus_MstWr_rem               : in  std_logic_vector(0 to 128/8-1); 
    IP2Bus_MstWr_sof_n             : in  std_logic;
    IP2Bus_MstWr_eof_n             : in  std_logic;
    IP2Bus_MstWr_src_rdy_n         : in  std_logic;
    IP2Bus_MstWr_src_dsc_n         : in  std_logic;
    Bus2IP_MstWr_dst_rdy_n         : out std_logic;
    Bus2IP_MstWr_dst_dsc_n         : out std_logic
    -- ADD USER PORTS ABOVE THIS LINE ------------------
  );

end entity plbv46_master_burst_wrapper;

------------------------------------------------------------------------------
-- Architecture section
------------------------------------------------------------------------------

architecture IMP of plbv46_master_burst_wrapper is

  constant PADDING_ZEROS                  : std_logic_vector(0 to 127) := (others => '0');
  
  ------------------------------------------
  -- IP Interconnect (IPIC) signal declarations
  ------------------------------------------
  -- NOT USED: signal ipif_IP2Bus_MstRd_Req          : std_logic;
  -- NOT USED: signal ipif_IP2Bus_MstWr_Req          : std_logic;
  -- NOT USED: signal ipif_IP2Bus_Mst_Addr           : std_logic_vector(0 to C_MPLB_AWIDTH-1);
  -- NOT USED: signal ipif_IP2Bus_Mst_Length         : std_logic_vector(0 to 11);
  -- NOT USED: signal ipif_IP2Bus_Mst_Type           : std_logic;
  -- NOT USED: signal ipif_IP2Bus_Mst_Lock           : std_logic;
  -- NOT USED: signal ipif_IP2Bus_Mst_Reset          : std_logic;
  -- NOT USED: signal ipif_Bus2IP_Mst_CmdAck         : std_logic;
  -- NOT USED: signal ipif_Bus2IP_Mst_Cmplt          : std_logic;
  -- NOT USED: signal ipif_Bus2IP_Mst_Error          : std_logic;
  -- NOT USED: signal ipif_Bus2IP_Mst_Rearbitrate    : std_logic;
  -- NOT USED: signal ipif_Bus2IP_Mst_Cmd_Timeout    : std_logic;
  -- NOT USED: signal ipif_Bus2IP_MstRd_sof_n        : std_logic;
  -- NOT USED: signal ipif_Bus2IP_MstRd_eof_n        : std_logic;
  -- NOT USED: signal ipif_Bus2IP_MstRd_src_rdy_n    : std_logic;
  -- NOT USED: signal ipif_Bus2IP_MstRd_src_dsc_n    : std_logic;
  -- NOT USED: signal ipif_IP2Bus_MstRd_dst_rdy_n    : std_logic;
  -- NOT USED: signal ipif_IP2Bus_MstRd_dst_dsc_n    : std_logic;
  -- NOT USED: signal ipif_IP2Bus_MstWr_sof_n        : std_logic;
  -- NOT USED: signal ipif_IP2Bus_MstWr_eof_n        : std_logic;
  -- NOT USED: signal ipif_IP2Bus_MstWr_src_rdy_n    : std_logic;
  -- NOT USED: signal ipif_IP2Bus_MstWr_src_dsc_n    : std_logic;
  -- NOT USED: signal ipif_Bus2IP_MstWr_dst_rdy_n    : std_logic;
  -- NOT USED: signal ipif_Bus2IP_MstWr_dst_dsc_n    : std_logic;
  
  -- 
  -- BITWIDTH ADAPTION:
  --
  --     Bitwidth of plbv46_master_burst is variable depending on the C_SPLB_DWIDTH/C_SPLB_NATIVE_DWIDTH
  --     Bitwidth of plbv46_master_burst_wrapper_128 is tuned for 128bit systemc modules
  -- 
  --     The following signals may have different bitwidth between 
  --     plbv46_master_burst and plbv46_master_burst_wrapper_128. And MSBs of them may not be connected
  --
  
  signal ipif_IP2Bus_Mst_BE             : std_logic_vector(0 to C_MPLB_NATIVE_DWIDTH/8-1);
  signal ipif_Bus2IP_MstRd_d            : std_logic_vector(0 to C_MPLB_NATIVE_DWIDTH-1);
  signal ipif_Bus2IP_MstRd_rem          : std_logic_vector(0 to C_MPLB_NATIVE_DWIDTH/8-1);
  signal ipif_IP2Bus_MstWr_d            : std_logic_vector(0 to C_MPLB_NATIVE_DWIDTH-1);
  signal ipif_IP2Bus_MstWr_rem          : std_logic_vector(0 to C_MPLB_NATIVE_DWIDTH/8-1);

begin

  ------------------------------------------
  -- instantiate plbv46_master_burst
  ------------------------------------------
  PLBV46_MASTER_BURST_I : entity plbv46_master_burst_v1_01_a.plbv46_master_burst
    generic map
    (
      C_MPLB_AWIDTH                  => C_MPLB_AWIDTH,
      C_MPLB_DWIDTH                  => C_MPLB_DWIDTH,
      C_MPLB_NATIVE_DWIDTH           => C_MPLB_NATIVE_DWIDTH,
      C_MPLB_SMALLEST_SLAVE          => C_MPLB_SMALLEST_SLAVE,
      C_INHIBIT_CC_BLE_INCLUSION     => C_INHIBIT_CC_BLE_INCLUSION,
      C_FAMILY                       => C_FAMILY
    )
    port map
    (
      MPLB_Clk                       => MPLB_Clk,
      MPLB_Rst                       => MPLB_Rst,
      MD_error                       => MD_error,
      M_request                      => M_request,
      M_priority                     => M_priority,
      M_busLock                      => M_busLock,
      M_RNW                          => M_RNW,
      M_BE                           => M_BE,
      M_MSize                        => M_MSize,
      M_size                         => M_size,
      M_type                         => M_type,
      M_TAttribute                   => M_TAttribute,
      M_lockErr                      => M_lockErr,
      M_abort                        => M_abort,
      M_UABus                        => M_UABus,
      M_ABus                         => M_ABus,
      M_wrDBus                       => M_wrDBus,
      M_wrBurst                      => M_wrBurst,
      M_rdBurst                      => M_rdBurst,
      PLB_MAddrAck                   => PLB_MAddrAck,
      PLB_MSSize                     => PLB_MSSize,
      PLB_MRearbitrate               => PLB_MRearbitrate,
      PLB_MTimeout                   => PLB_MTimeout,
      PLB_MBusy                      => PLB_MBusy,
      PLB_MRdErr                     => PLB_MRdErr,
      PLB_MWrErr                     => PLB_MWrErr,
      PLB_MIRQ                       => PLB_MIRQ,
      PLB_MRdDBus                    => PLB_MRdDBus,
      PLB_MRdWdAddr                  => PLB_MRdWdAddr,
      PLB_MRdDAck                    => PLB_MRdDAck,
      PLB_MRdBTerm                   => PLB_MRdBTerm,
      PLB_MWrDAck                    => PLB_MWrDAck,
      PLB_MWrBTerm                   => PLB_MWrBTerm,
      IP2Bus_MstRd_Req               => IP2Bus_MstRd_Req,
      IP2Bus_MstWr_Req               => IP2Bus_MstWr_Req,
      IP2Bus_Mst_Addr                => IP2Bus_Mst_Addr,
      IP2Bus_Mst_Length              => IP2Bus_Mst_Length,
      IP2Bus_Mst_BE                  => ipif_IP2Bus_Mst_BE,             ---- FOR BITWIDTH ADAPTION
      IP2Bus_Mst_Type                => IP2Bus_Mst_Type,
      IP2Bus_Mst_Lock                => IP2Bus_Mst_Lock,
      IP2Bus_Mst_Reset               => IP2Bus_Mst_Reset,
      Bus2IP_Mst_CmdAck              => Bus2IP_Mst_CmdAck,
      Bus2IP_Mst_Cmplt               => Bus2IP_Mst_Cmplt,
      Bus2IP_Mst_Error               => Bus2IP_Mst_Error,
      Bus2IP_Mst_Rearbitrate         => Bus2IP_Mst_Rearbitrate,
      Bus2IP_Mst_Cmd_Timeout         => Bus2IP_Mst_Cmd_Timeout,
      Bus2IP_MstRd_d                 => ipif_Bus2IP_MstRd_d,            ---- FOR BITWIDTH ADAPTION
      Bus2IP_MstRd_rem               => ipif_Bus2IP_MstRd_rem,          ---- FOR BITWIDTH ADAPTION
      Bus2IP_MstRd_sof_n             => Bus2IP_MstRd_sof_n,
      Bus2IP_MstRd_eof_n             => Bus2IP_MstRd_eof_n,
      Bus2IP_MstRd_src_rdy_n         => Bus2IP_MstRd_src_rdy_n,
      Bus2IP_MstRd_src_dsc_n         => Bus2IP_MstRd_src_dsc_n,
      IP2Bus_MstRd_dst_rdy_n         => IP2Bus_MstRd_dst_rdy_n,
      IP2Bus_MstRd_dst_dsc_n         => IP2Bus_MstRd_dst_dsc_n,
      IP2Bus_MstWr_d                 => ipif_IP2Bus_MstWr_d,            ---- FOR BITWIDTH ADAPTION
      IP2Bus_MstWr_rem               => ipif_IP2Bus_MstWr_rem,          ---- FOR BITWIDTH ADAPTION
      IP2Bus_MstWr_sof_n             => IP2Bus_MstWr_sof_n,
      IP2Bus_MstWr_eof_n             => IP2Bus_MstWr_eof_n,
      IP2Bus_MstWr_src_rdy_n         => IP2Bus_MstWr_src_rdy_n,
      IP2Bus_MstWr_src_dsc_n         => IP2Bus_MstWr_src_dsc_n,
      Bus2IP_MstWr_dst_rdy_n         => Bus2IP_MstWr_dst_rdy_n,
      Bus2IP_MstWr_dst_dsc_n         => Bus2IP_MstWr_dst_dsc_n
    );
    
    ipif_IP2Bus_Mst_BE <= IP2Bus_Mst_BE(128/8-C_MPLB_NATIVE_DWIDTH/8 to 128/8-1);
    ipif_IP2Bus_MstWr_d <= IP2Bus_MstWr_d(128-C_MPLB_NATIVE_DWIDTH to 128-1);
    ipif_IP2Bus_MstWr_rem <= IP2Bus_MstWr_rem(128/8-C_MPLB_NATIVE_DWIDTH/8 to 128/8-1);
    
    Bus2IP_MstRd_d <= PADDING_ZEROS(C_MPLB_NATIVE_DWIDTH to 128-1) & ipif_Bus2IP_MstRd_d;
    Bus2IP_MstRd_rem <= PADDING_ZEROS(C_MPLB_NATIVE_DWIDTH/8 to 16-1) & ipif_Bus2IP_MstRd_rem;
    
    Bus2IP_Mst_Clk <= MPLB_Clk;
    Bus2IP_Mst_Reset <= MPLB_Rst;

end IMP;
