-------------------------------------------------------------------------------   
-- icap_wrapper.vhd
------------------------------------------------------------------------------- 

library IEEE;
use IEEE.std_logic_1164.all;

library unisim;
use unisim.vcomponents.all;

-------------------------------------------------------------------------------
-- Definition of Generics:
--  C_RESIM             -- Parameter is TRUE for ReSim-based simulation
--  C_FAMILY            -- target FPGA family
-------------------------------------------------------------------------------
-- --inputs
--
--  Icap_clk            -- ICAP clock
--  Icap_ce             -- ICAP chip enable
--  Icap_we             -- ICAP write enable
--  Icap_datain         -- ICAP configuration data in
--  
-- --outputs
--
--  Icap_busy           -- ICAP busy qualifier
--  Icap_dataout        -- ICAP configuration readback data out
-------------------------------------------------------------------------------

entity icap_wrapper is
    generic(
        C_RESIM             : integer := 1;
        C_GEN_BITSWAP       : integer := 1;
        C_FAMILY            : string  := "virtex5"
    );
    port(
        Icap_clk            : in  std_logic;
        Icap_ce             : in  std_logic;
        Icap_we             : in  std_logic;
        Icap_datain         : in  std_logic_vector(31 downto 0);
        Icap_busy           : out std_logic;
        Icap_dataout        : out std_logic_vector(31 downto 0)
    );
    
    attribute KEEP : string;
    attribute KEEP of Icap_ce : signal is "TRUE";
    attribute KEEP of Icap_we : signal is "TRUE";
    attribute KEEP of Icap_datain : signal is "TRUE";
    attribute KEEP of Icap_dataout : signal is "TRUE";
    attribute KEEP of Icap_busy : signal is "TRUE";

end icap_wrapper;

architecture imp of icap_wrapper is

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

    component ICAP_VIRTEX6 is
        generic(
            ICAP_WIDTH  : string := "X8"
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

    component ICAP_VIRTEX4_WRAPPER is
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

    component ICAP_VIRTEX5_WRAPPER is
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

    component ICAP_VIRTEX6_WRAPPER is
        generic(
            ICAP_WIDTH  : string := "X8"
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

	signal Icap_datain_bs  : std_logic_vector(31 downto 0);
	signal Icap_dataout_bs : std_logic_vector(31 downto 0);
	
begin  -- architecture imp

    -----------------------------------------------------------------------------
    -- GEN_UNISIM
    -----------------------------------------------------------------------------
    -- Implement using ICAP instance on chip
    -- Simulate using unisim model (black box)
    
    GEN_UNISIM : if C_RESIM = 0 generate

        GEN_VIRTEX4 : if (C_FAMILY="virtex4") generate
            ICAP_VERTEX4_I : ICAP_VIRTEX4
                generic map (
                    ICAP_WIDTH => "X32")
                port map (
                    CLK        => Icap_clk,
                    CE         => Icap_ce,
                    WRITE      => Icap_we,
                    I          => Icap_datain_bs,
                    BUSY       => Icap_busy,
                    O          => Icap_dataout_bs
                );
        end generate GEN_VIRTEX4;

        GEN_VIRTEX5 : if (C_FAMILY="virtex5") generate
            ICAP_VERTEX5_I : ICAP_VIRTEX5
                generic map (
                    ICAP_WIDTH => "X32")
                port map (
                    CLK        => icap_clk,
                    CE         => icap_ce,
                    WRITE      => icap_we,
                    I          => icap_datain_bs,
                    BUSY       => icap_busy,
                    O          => icap_dataout_bs
                );
        end generate GEN_VIRTEX5;

        GEN_VIRTEX6 : if (C_FAMILY="virtex6") generate
            ICAP_VERTEX6_I : ICAP_VIRTEX6
                generic map (
                    ICAP_WIDTH => "X32")
                port map (
                    CLK        => icap_clk,
                    CSB        => icap_ce,
                    RDWRB      => icap_we,
                    I          => icap_datain_bs,
                    BUSY       => icap_busy,
                    O          => icap_dataout_bs
                );
        end generate GEN_VIRTEX6;

    end generate GEN_UNISIM;

    -----------------------------------------------------------------------------
    -- GEN_RESIM:
    -----------------------------------------------------------------------------
    -- Implement using ICAP instance on chip
    -- Simulate using ReSim model
    
    GEN_RESIM : if C_RESIM = 1 generate

        GEN_VIRTEX4 : if (C_FAMILY="virtex4") generate
            ICAP_VIRTEX4_I : ICAP_VIRTEX4_WRAPPER
                generic map (
                    ICAP_WIDTH => "X32"
                )
                port map (
                    CLK        => icap_clk,        -- I: clock
                    CE         => icap_ce,         -- I: clock enable
                    WRITE      => icap_we,         -- I: write enable
                    I          => icap_datain_bs,  -- I: configuration data
                    BUSY       => icap_busy,       -- O: busy
                    O          => icap_dataout_bs  -- O: configuration readback data
                );
        end generate GEN_VIRTEX4;

        GEN_VIRTEX5 : if (C_FAMILY="virtex5") generate
            ICAP_VIRTEX5_I : ICAP_VIRTEX5_WRAPPER
                generic map (
                    ICAP_WIDTH => "X32"
                )
                port map (
                    CLK        => icap_clk,        -- I: clock
                    CE         => icap_ce,         -- I: clock enable
                    WRITE      => icap_we,         -- I: write enable
                    I          => icap_datain_bs,  -- I: configuration data
                    BUSY       => icap_busy,       -- O: busy
                    O          => icap_dataout_bs  -- O: configuration readback data
                );
        end generate GEN_VIRTEX5;

        GEN_VIRTEX6 : if (C_FAMILY="virtex6") generate
            ICAP_VIRTEX6_I : ICAP_VIRTEX6_WRAPPER
                generic map (
                    ICAP_WIDTH => "X32"
                )
                port map (
                    CLK        => icap_clk,        -- I: clock
                    CSB        => icap_ce,         -- I: clock enable
                    RDWRB      => icap_we,         -- I: write enable
                    I          => icap_datain_bs,  -- I: configuration data
                    BUSY       => icap_busy,       -- O: busy
                    O          => icap_dataout_bs  -- O: configuration readback data
                );
        end generate GEN_VIRTEX6;

    end generate GEN_RESIM;

    -----------------------------------------------------------------------------
    -- GEN_BITSWAP:
    -----------------------------------------------------------------------------
    
	----SystemVerilog Syntax
	----
	----generate begin : gen_i_bitswap
	----	genvar j;
	----	for (j = 0; j <= 3; j = j + 1) begin : mirror_j
	----		genvar i;
	----		for (i = 0; i <= 7; i = i + 1) begin : mirror_i
	----			assign I_bs[j * 8 + i] = I[j * 8 + 7 - i];
	----		end
	----	end
	----end endgenerate
	----
	----generate begin : gen_o_bitswap
	----	genvar j;
	----	for (j = 0; j <= 3; j = j + 1) begin : mirror_j
	----		genvar i;
	----		for (i = 0; i <= 7; i = i + 1) begin : mirror_i
	----			assign O[j * 8 + i] = O_bs[j * 8 + 7 - i];
	----		end
	----	end
	----end endgenerate
	
	GEN_NO_BITSWAP : if ((C_FAMILY = "virtex4") or (C_GEN_BITSWAP = 0)) generate
		
		Icap_datain_bs <= Icap_datain;
		Icap_dataout <= Icap_dataout_bs;
		
	end generate GEN_NO_BITSWAP;
	
	GEN_VERITEX5_BS : if ((C_FAMILY = "virtex5") and (C_GEN_BITSWAP = 1)) generate
	
		process(Icap_datain) begin
			for j in 0 to 3 loop
				for i in 0 to 7 loop
					Icap_datain_bs(j * 8 + i) <= Icap_datain(j * 8 + 7 - i);
				end loop;
			end loop;
		end process;
		
		process(Icap_dataout_bs) begin
			for j in 0 to 3 loop
				for i in 0 to 7 loop
					Icap_dataout(j * 8 + i) <= Icap_dataout_bs(j * 8 + 7 - i);
				end loop;
			end loop;
		end process;
		
	end generate GEN_VERITEX5_BS;
	
	GEN_VERITEX6_BS : if ((C_FAMILY = "virtex6") and (C_GEN_BITSWAP = 1)) generate
	
		process(Icap_datain) begin
			for j in 0 to 3 loop
				for i in 0 to 7 loop
					Icap_datain_bs(j * 8 + i) <= Icap_datain(j * 8 + 7 - i);
				end loop;
			end loop;
		end process;
		
		process(Icap_dataout_bs) begin
			for j in 0 to 3 loop
				for i in 0 to 7 loop
					Icap_dataout(j * 8 + i) <= Icap_dataout_bs(j * 8 + 7 - i);
				end loop;
			end loop;
		end process;
		
	end generate GEN_VERITEX6_BS;
	
end architecture imp;



