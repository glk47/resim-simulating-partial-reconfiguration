
---------------------------------------------------------------------
--
-- ICAP_VIRTEX4_WRAPPER 
--
-- Description: Instantiating ICAP_VIRTEX4
-- Simulation/Synthesis: Synthesis
-- Reference: $XILINX_HOME/vhdl/src/unisims/primitive/ICAP_VIRTEX4.vhd
--
---------------------------------------------------------------------

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

library UNISIM;
use UNISIM.VComponents.all;

entity ICAP_VIRTEX4_WRAPPER is
	generic(
		ICAP_WIDTH: string := "X8" -- "X8" or "X32"
	);
	port(
		BUSY  : out std_logic;
		O     : out std_logic_vector(31 downto 0);
		
		CE    : in  std_logic;
		CLK   : in  std_logic;
		I     : in  std_logic_vector(31 downto 0);
		WRITE : in  std_logic
	);
end ICAP_VIRTEX4_WRAPPER;

architecture synth of ICAP_VIRTEX4_WRAPPER is 

	component ICAP_VIRTEX4 is
		generic(
			ICAP_WIDTH  : string := "X8"
		);
		port(
			CLK         : in  std_logic;
			CE          : in  std_logic;
			WRITE       : in  std_logic;
			I           : in  std_logic_vector(31 downto 0);
			BUSY        : out std_logic;
			O           : out std_logic_vector(31 downto 0)
		);
	end component;
	
begin

	i_ICAP_VIRTEX4 : ICAP_VIRTEX4
		generic map (
			ICAP_WIDTH => ICAP_WIDTH
		) 
		port map (
			BUSY  => BUSY,
			O     => O,
			CE    => CE,
			CLK   => CLK,
			I     => I,
			WRITE => WRITE
	);

end synth;

---------------------------------------------------------------------
--
-- ICAP_VIRTEX5_WRAPPER 
--
-- Description: Instantiating ICAP_VIRTEX5
-- Simulation/Synthesis: Synthesis
-- Reference: $XILINX_HOME/vhdl/src/unisims/primitive/ICAP_VIRTEX5.vhd
--
---------------------------------------------------------------------

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

library UNISIM;
use UNISIM.VComponents.all;

entity ICAP_VIRTEX5_WRAPPER is
	generic(
		ICAP_WIDTH: string := "X8" -- "X8", "X16" or "X32"
	);
	port(
		BUSY  : out std_logic;
		O     : out std_logic_vector(31 downto 0);
		
		CE    : in  std_logic;
		CLK   : in  std_logic;
		I     : in  std_logic_vector(31 downto 0);
		WRITE : in  std_logic
	);
end ICAP_VIRTEX5_WRAPPER;

architecture synth of ICAP_VIRTEX5_WRAPPER is 

	component ICAP_VIRTEX5 is
		generic(
			ICAP_WIDTH  : string := "X8"
		);
		port(
			CLK         : in  std_logic;
			CE          : in  std_logic;
			WRITE       : in  std_logic;
			I           : in  std_logic_vector(31 downto 0);
			BUSY        : out std_logic;
			O           : out std_logic_vector(31 downto 0)
		);
	end component;
	
begin

	i_ICAP_VIRTEX5 : ICAP_VIRTEX5
		generic map (
			ICAP_WIDTH => ICAP_WIDTH
		) 
		port map (
			BUSY  => BUSY,
			O     => O,
			CE    => CE,
			CLK   => CLK,
			I     => I,
			WRITE => WRITE
	);

end synth;

---------------------------------------------------------------------
--
-- ICAP_VIRTEX6_WRAPPER 
--
-- Description: Instantiating ICAP_VIRTEX6
-- Simulation/Synthesis: Synthesis
-- Reference: $XILINX_HOME/vhdl/src/unisims/primitive/ICAP_VIRTEX6.vhd
--
---------------------------------------------------------------------

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

library UNISIM;
use UNISIM.VComponents.all;

entity ICAP_VIRTEX6_WRAPPER is
	generic(
		DEVICE_ID : bit_vector := X"04244093";
		ICAP_WIDTH : string := "X8"; -- "X8", "X16" or "X32"
		SIM_CFG_FILE_NAME : string := "NONE"
	);
	port(
		BUSY  : out std_logic;
		O     : out std_logic_vector(31 downto 0);
		
		CSB   : in  std_logic;
		CLK   : in  std_logic;
		I     : in  std_logic_vector(31 downto 0);
		RDWRB : in  std_logic
	);
end ICAP_VIRTEX6_WRAPPER;

architecture synth of ICAP_VIRTEX6_WRAPPER is 

	component ICAP_VIRTEX6 is
		generic(
			DEVICE_ID : bit_vector := X"04244093";
			ICAP_WIDTH : string := "X8";
			SIM_CFG_FILE_NAME : string := "NONE"
		);
		port(
			CLK         : in  std_logic;
			CSB         : in  std_logic;
			RDWRB       : in  std_logic;
			I           : in  std_logic_vector(31 downto 0);
			BUSY        : out std_logic;
			O           : out std_logic_vector(31 downto 0)
		);
	end component;
	
begin

	i_ICAP_VIRTEX6 : ICAP_VIRTEX6
		generic map (
			DEVICE_ID         => DEVICE_ID,
			ICAP_WIDTH        => ICAP_WIDTH,
			SIM_CFG_FILE_NAME => SIM_CFG_FILE_NAME
		)
		port map (
			BUSY  => BUSY,
			O     => O,
			CSB   => CSB,
			CLK   => CLK,
			I     => I,
			RDWRB => RDWRB
	);

end synth;

