//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: State_Migration
//
// Create Date:    12/06/2010
// Design Name:    icapi_regs
//
//---------------------------------------------------------------------

`timescale 1ns/1ns

module icapi_regs # (
	parameter C_DWIDTH          = 128,
	parameter C_MEM_BASEADDR    = 'hffffffff,
	parameter C_MEM_HIGHADDR    = 'h00000000
)
(
	input                       Bus2IP_Clk,
	input                       Bus2IP_Reset,
	input      [31:0]           Bus2IP_Addr,
	input                       Bus2IP_CS,
	input                       Bus2IP_RNW,
	input      [C_DWIDTH-1:0]   Bus2IP_Data,
	input      [C_DWIDTH/8-1:0] Bus2IP_BE,
	input                       Bus2IP_Burst,
	input      [8:0]            Bus2IP_BurstLength,
	input                       Bus2IP_RdReq,
	input                       Bus2IP_WrReq,
	output reg                  IP2Bus_AddrAck,
	output     [C_DWIDTH-1:0]   IP2Bus_Data,
	output reg                  IP2Bus_RdAck,
	output reg                  IP2Bus_WrAck,
	output                      IP2Bus_Error,
	
	output                      soft_reset,
	output                      rc_start,
	output                      rc_bop,
	output     [31:0]           rc_baddr,
	output     [31:0]           rc_bsize,
	input                       rc_done,
	
	output                      IP2INTC_Irpt
);
	
	`define ICAPI_OP_RdCfg 'h0
	`define ICAPI_OP_WrCfg 'h1
	
	`define ICAPI_IS_BUSY  'h0
	`define ICAPI_IS_DONE  'h1
	`define ICAPI_IS_ERROR 'h3

	reg [31:0]  m_ctrl;
	reg [31:0]  m_stat;
	reg [31:0]  m_bitstream_addr; // Bitstream Address in bytes
	reg [31:0]  m_bitstream_size; // Bitstream Size in bytes
	reg [31:0]  m_ier;

	reg [31:0]  read_data;    // MSB 32bit of IP2Bus_Data
	wire [31:0] written_data; // MSB 32bit of Bus2IP_Data
	
	 // WAR: For 128bit, the valid data does not always appear on MSB
	 // In fact, the valid bit position is defined by BE
	 // So the following code actually only support 32bit DWidth
	
	generate begin if (C_DWIDTH>32)
		assign IP2Bus_Data[C_DWIDTH-32-1:0] = {C_DWIDTH-32{1'b0}};
	end endgenerate
	assign IP2Bus_Data[C_DWIDTH-1:C_DWIDTH-32] = read_data;
	
	assign written_data = Bus2IP_Data[C_DWIDTH-1:C_DWIDTH-32]; 
	
//-------------------------------------------------------------------
// Read Regs
//-------------------------------------------------------------------
	
	always @(posedge Bus2IP_Clk or posedge Bus2IP_Reset) begin
		if (Bus2IP_Reset) begin
			IP2Bus_AddrAck <= 1'b0;
			IP2Bus_RdAck <= 1'b0;
			IP2Bus_WrAck <= 1'b0;
		end else begin
			IP2Bus_AddrAck <= (Bus2IP_RdReq || Bus2IP_WrReq);
			IP2Bus_RdAck <= Bus2IP_RdReq;
			IP2Bus_WrAck <= Bus2IP_WrReq;
		end
	end
	
	always @(posedge Bus2IP_Clk or posedge Bus2IP_Reset) begin
		if (Bus2IP_Reset) begin
			read_data <= 32'h0;
		end else begin
			if (Bus2IP_RdReq) begin
				case (Bus2IP_Addr-C_MEM_BASEADDR)
					16'h0: begin read_data <= m_ctrl ; end
					16'h4: begin read_data <= m_stat ; end
					16'h8: begin read_data <= m_bitstream_addr ; end
					16'hc: begin read_data <= m_bitstream_size ; end
					16'h10: begin read_data <= m_ier ; end
					default: begin end
				endcase
			end
		end
	end
	assign IP2Bus_Error = 1'b0;
	
	// TODO: assert BE == 0xffff ....
	// TODO: assert Address == %4 ....
	// TODO: assert Type == SINGLE_BEAT
	
//-------------------------------------------------------------------
// m_bitstream_addr
// m_bitstream_size
// m_ier
//-------------------------------------------------------------------

	always @(posedge Bus2IP_Clk or posedge Bus2IP_Reset) begin
		if (Bus2IP_Reset) begin
			m_bitstream_addr <= 32'h0;
			m_bitstream_size <= 32'h0;
			m_ier <= 32'h0;
		end else begin
			if (Bus2IP_WrReq) begin
				case (Bus2IP_Addr-C_MEM_BASEADDR)
					16'h8: begin  m_bitstream_addr <= written_data; end
					16'hc: begin  m_bitstream_size <= written_data; end
					16'h10: begin m_ier <= written_data; end
					default: begin end
				endcase
			end
		end
	end
	assign rc_baddr = m_bitstream_addr >> 2; // rc_baddr: Bitstream Size in WORDS
	assign rc_bsize = m_bitstream_size >> 2; // rc_bsize: Bitstream Size in WORDS
	
//-------------------------------------------------------------------
// m_ctrl
//-------------------------------------------------------------------

	always @(posedge Bus2IP_Clk or posedge Bus2IP_Reset) begin
		if (Bus2IP_Reset) begin
			m_ctrl <= 32'h0;
		end else begin
			if ((Bus2IP_WrReq) && ((Bus2IP_Addr-C_MEM_BASEADDR)==32'h0)) begin
				
				if (written_data[31]) begin // TODO: Soft Reset
					m_ctrl[31]   <= 1'b1;
					m_ctrl[30:0] <= 'h0;
				end else if (m_stat!=`ICAPI_IS_BUSY) begin
					m_ctrl <= written_data;
				end
				
			end else begin
				m_ctrl[31] <= 1'b0; // ICAPI_RESET only last one cycle
				m_ctrl[0]  <= 1'b0; // ICAPI_START only last one cycle
			end
			
		end
	end
	assign soft_reset = m_ctrl[31];// ICAPI_RESET == 1
	assign rc_bop     = m_ctrl[1]; // ICAPI_OP
	assign rc_start   = m_ctrl[0]; // ICAPI_START == 1: Start ICAPI && Clear m_stat
	
//-------------------------------------------------------------------
// m_stat
// IP2INTC_Irpt
//-------------------------------------------------------------------
	
	always @(posedge Bus2IP_Clk or posedge Bus2IP_Reset) begin
		if (Bus2IP_Reset) begin
			m_stat <= `ICAPI_IS_DONE;
		end else begin
			if (rc_start) m_stat <= `ICAPI_IS_BUSY;     // NOTE: One cycle later than rc_start
			else if (rc_done) m_stat <= `ICAPI_IS_DONE; // NOTE: One cycle later than rc_done
			
		end
	end
	assign IP2INTC_Irpt = ((m_stat == `ICAPI_IS_DONE) && m_ier[31]); // SIGIS = INTERRUPT, SENSITIVITY = LEVEL_HIGH

endmodule
