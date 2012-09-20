//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: State_Migration
//
// Create Date:    12/06/2010
// Design Name:    xbus_masterif
//
//---------------------------------------------------------------------

`timescale 1ns/1ns

module xbus_masterif # (
	parameter C_DWIDTH          = 128
)
(
	//-- to/form ipif ----
	input                       Bus2IP_Mst_Clk,
	input                       Bus2IP_Mst_Reset,
	output                      IP2Bus_MstRd_Req,
	output                      IP2Bus_MstWr_Req,
	output     [31:0]           IP2Bus_Mst_Addr,
	output     [C_DWIDTH/8-1:0] IP2Bus_Mst_BE,
	output     [11:0]           IP2Bus_Mst_Length,
	output                      IP2Bus_Mst_Type,
	output                      IP2Bus_Mst_Lock,
	output                      IP2Bus_Mst_Reset,
	input                       Bus2IP_Mst_CmdAck,
	input                       Bus2IP_Mst_Cmplt,
	input                       Bus2IP_Mst_Error,
	input                       Bus2IP_Mst_Rearbitrate,
	input                       Bus2IP_Mst_Cmd_Timeout,
	input      [C_DWIDTH-1:0]   Bus2IP_MstRd_d,
	input      [C_DWIDTH/8-1:0] Bus2IP_MstRd_rem,
	input                       Bus2IP_MstRd_sof_n,
	input                       Bus2IP_MstRd_eof_n,
	input                       Bus2IP_MstRd_src_rdy_n,
	input                       Bus2IP_MstRd_src_dsc_n,
	output                      IP2Bus_MstRd_dst_rdy_n,
	output                      IP2Bus_MstRd_dst_dsc_n,
	output     [C_DWIDTH-1:0]   IP2Bus_MstWr_d,
	output     [C_DWIDTH/8-1:0] IP2Bus_MstWr_rem,
	output                      IP2Bus_MstWr_sof_n,
	output                      IP2Bus_MstWr_eof_n,
	output                      IP2Bus_MstWr_src_rdy_n,
	output                      IP2Bus_MstWr_src_dsc_n,
	input                       Bus2IP_MstWr_dst_rdy_n,
	input                       Bus2IP_MstWr_dst_dsc_n,
	
	//-- to/from xbus (xbus master interface)----
	input                       ma_req        ,
	output                      xbm_gnt       ,
	input                       ma_select     ,
	input      [31:0]           ma_addr       ,
	input      [31:0]           ma_data       ,
	input                       ma_rnw        ,
	input      [3:0]            ma_be         ,
	output                      xbm_ack       ,
	output     [31:0]           xbm_data      
);
	
	`define IDLE      8'h0
	`define ADDR      8'h1
	`define ADDR_DATA 8'h2
	`define DATA_ADDR 8'h3
	`define COMP      8'h4
	
//-------------------------------------------------------------------
// Request & Ack
//-------------------------------------------------------------------

	wire master_rd_req, master_wr_req; // Internal request
	wire master_rd_ack, master_wr_ack; // Internal acknowledge
	
	wire [31:0]           master_address;
	reg  [31:0]           master_rd_data;
	wire [C_DWIDTH-1:0]   master_wr_data;
	reg  [C_DWIDTH/8-1:0] master_byte_enable;
	
	reg [7:0] state_c, state_n;
	
	assign master_rd_req = ma_select & ma_rnw;
	assign master_wr_req = ma_select & ~ma_rnw;
	
	assign master_rd_ack = (~Bus2IP_MstRd_src_rdy_n & ~IP2Bus_MstRd_dst_rdy_n & ~Bus2IP_MstRd_sof_n & ~Bus2IP_MstRd_eof_n);
	assign master_wr_ack = (~IP2Bus_MstWr_src_rdy_n & ~Bus2IP_MstWr_dst_rdy_n & ~IP2Bus_MstWr_sof_n & ~IP2Bus_MstWr_eof_n);
	
	generate begin : gen_master_wr_data
		genvar i;
		for (i = 0; i < C_DWIDTH/32; i = i + 1) begin : mirror_j
			assign master_wr_data[C_DWIDTH-1-32*i:C_DWIDTH-32-32*i] = ma_data;
		end
	end endgenerate
	
	always @(*) begin
		case (ma_addr[1:0])
			0: begin master_byte_enable = 16'hf000; end
			1: begin master_byte_enable = 16'h0f00; end
			2: begin master_byte_enable = 16'h00f0; end
			3: begin master_byte_enable = 16'h000f; end
			default: begin master_byte_enable = 16'h0000; end
		endcase
	end
	
	always @(posedge Bus2IP_Mst_Clk or posedge Bus2IP_Mst_Reset) begin
		if (Bus2IP_Mst_Reset)
			master_rd_data <= 32'h0;
		else begin
			if (master_rd_ack) begin
				case (Bus2IP_MstRd_rem)
					16'h0fff: begin master_rd_data <= Bus2IP_MstRd_d[127:96]; end
					16'hf0ff: begin master_rd_data <= Bus2IP_MstRd_d[95:64]; end
					16'hff0f: begin master_rd_data <= Bus2IP_MstRd_d[63:32]; end
					16'hfff0: begin master_rd_data <= Bus2IP_MstRd_d[31:0]; end
					default: begin master_rd_data <= 32'h0; end
				endcase
			end
		end
	end
	
	assign master_address = {ma_addr[29:0],2'b0}; // IP use address in WORDS
	
//-------------------------------------------------------------------
// Main FSM
//-------------------------------------------------------------------

	always @(posedge Bus2IP_Mst_Clk or posedge Bus2IP_Mst_Reset) begin
		if (Bus2IP_Mst_Reset)
			state_c <= `IDLE;
		else
			state_c <= state_n;
	end
	
	always @(*) begin
		case (state_c)
			`IDLE: begin state_n = (master_rd_req || master_wr_req)? `ADDR: `IDLE; end
			`ADDR: begin 
				state_n = `ADDR;
				if (Bus2IP_Mst_CmdAck) state_n = `ADDR_DATA;
				if (master_rd_ack || master_wr_ack) state_n = `DATA_ADDR;
			end
			`ADDR_DATA: begin state_n = (master_rd_ack || master_wr_ack)?`COMP: `ADDR_DATA; end
			`DATA_ADDR: begin state_n = (Bus2IP_Mst_CmdAck)?`COMP: `DATA_ADDR; end
			`COMP: begin state_n = (Bus2IP_Mst_Cmplt)? `IDLE: `COMP; end
			default: begin state_n = `IDLE; end
		endcase
	end
	
	// synthesis translate_off
	reg  [8*20:1] state_ascii;
	always @(*) begin
		if      (state_c==`IDLE)      state_ascii <= "IDLE";
		else if (state_c==`ADDR)      state_ascii <= "ADDR";
		else if (state_c==`ADDR_DATA) state_ascii <= "ADDR_DATA";
		else if (state_c==`DATA_ADDR) state_ascii <= "DATA_ADDR";
		else if (state_c==`COMP)      state_ascii <= "COMP";
		else                          state_ascii <= "ERROR";
	end
	// synthesis translate_on
	
//-------------------------------------------------------------------
// IPIF <-> XBUS_IF
//-------------------------------------------------------------------
	
	assign IP2Bus_MstRd_Req  = master_rd_req && ((state_c == `ADDR) || (state_c == `DATA_ADDR));
	assign IP2Bus_MstWr_Req  = master_wr_req && ((state_c == `ADDR) || (state_c == `DATA_ADDR));
	
	assign IP2Bus_Mst_Addr   = master_address;
	assign IP2Bus_Mst_BE     = master_byte_enable;
	assign IP2Bus_Mst_Length = 'h0; // Always C_DWIDTH/8 bytes
	assign IP2Bus_Mst_Type   = 'h0; // Always single beat transfer
	assign IP2Bus_Mst_Lock   = 'h0;
	assign IP2Bus_Mst_Reset  = 'h0;

	assign IP2Bus_MstRd_dst_rdy_n = ~(master_rd_req && ((state_c == `ADDR)||(state_c == `ADDR_DATA)||(state_c == `DATA_ADDR)));
	assign IP2Bus_MstRd_dst_dsc_n = 1'b1;
	assign IP2Bus_MstWr_d         = master_wr_data;      // IP Write Bus
	assign IP2Bus_MstWr_rem       = ~master_byte_enable; // IP Write Bus
	assign IP2Bus_MstWr_sof_n     = ~ma_select;
	assign IP2Bus_MstWr_eof_n     = ~ma_select;
	assign IP2Bus_MstWr_src_rdy_n = ~(master_wr_req && ((state_c == `ADDR)||(state_c == `ADDR_DATA)||(state_c == `DATA_ADDR)));
	assign IP2Bus_MstWr_src_dsc_n = 1'b1;
	
	assign xbm_gnt = 1'b1; // Point-to-point connection: ma_req not used + always grant
	assign xbm_data = master_rd_data;   // IP Read Bus
	assign xbm_ack  = Bus2IP_Mst_Cmplt; // Acknowledge XBUS_IF at the very last cycle
	
endmodule
