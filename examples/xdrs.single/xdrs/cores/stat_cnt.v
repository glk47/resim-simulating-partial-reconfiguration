/*******************************************************************

 Company: UNSW
 Original Author: Lingkan Gong
 Project Name: XDRS

 Create Date:    19/09/2010
 Design Name:    stat_cnt

 *******************************************************************/

`timescale 1ns/1ns

module stat_cnt
#(parameter
	C_CNT_BW = 32
)
(
	input       clk       ,
	input       rstn      ,

	//-- to/from the datapath to be monitored----
	input      [31:0] din,
	input      [31:0] dout,
	input      din_valid,
	input      dout_valid
);

//-------------------------------------------------------------------
// Signal Declaration
//-------------------------------------------------------------------

	// indata & incnt register
	reg [31:0] indata;
	reg [C_CNT_BW-1:0] incnt;

	// outdata & outcnt register
	reg [31:0] outdata;
	reg [C_CNT_BW-1:0] outcnt;

	// dummy signals
	wire [31:0] dummy_signal_0; reg [31:0] dummy_signal_1;
	
//-------------------------------------------------------------------
// Statistic Registers
//-------------------------------------------------------------------

	/* indata & incnt register */
	always @(posedge clk or negedge rstn) begin
		if (~rstn) begin
			indata <= 32'h0;
			incnt <= 'h0; // .OR. {C_CNT_BW{1'b0}};
		end else begin
			if (din_valid) indata <= din;
			if (din_valid) incnt <= incnt + 'h1; 
		end
	end

	/* outdata & outcnt register */
	always @(posedge clk or negedge rstn) begin
		if (~rstn) begin
			outdata <= 32'h0;
			outcnt <= {C_CNT_BW{1'b0}};
		end else begin
			if (dout_valid) outdata <= dout;
			if (dout_valid) outcnt <= outcnt + 'h1;
		end
	end

/* 
	always @(posedge clk or negedge rstn) begin
		if (~rstn)
			reg_dout <= 32'h0;
		else
			if (reg_rd_en) begin
				case (reg_addr)

					(XADDRBASE + 12'h00) : reg_dout <= indata;
					(XADDRBASE + 12'h04) : reg_dout <= incnt;
					(XADDRBASE + 12'h08) : reg_dout <= outdata;
					(XADDRBASE + 12'h0c) : reg_dout <= outcnt;

					default: reg_dout <= 32'h0;
				endcase
			end
	end
*/

	/* dummy signals */
	assign dummy_signal_0 = outdata; 
	always @(*) begin dummy_signal_1 = outdata; end
	
endmodule


/*

//-------------------------------------------------------------------
// Register Definitions
//-------------------------------------------------------------------
	`define reg_begin(_name)                                       \
	always @(posedge clk or negedge rstn) begin                     \
		if (~rstn)                                                   \
			_name <= 32'h0;                                        \
		else begin

	`define reg_end(_name)                                         \
		end                                                        \
	end

	`define map_to_address(_name, _addr)                           \
			if ((reg_addr==_addr) && reg_wr_en)                    \
				_name <= reg_din;

	`define delay_1c(_name, _var)                                  \
	always @(posedge clk or negedge ~rstn)                           \
		if(~rstn) _name <= 1'b0; else _name <= _var;

	`define delay_1c_cond(_name, _var, _cond)                      \
	always @(posedge clk or negedge rstn)                           \
		if(~rstn) _name <= 1'b0; else if (_cond) _name <= _var;

//-------------------------------------------------------------------
// Statistic Registers
//-------------------------------------------------------------------
	`reg_begin(indata)
		if (din_valid) indata <= din;
	`reg_end(indata)
	`reg_begin(incnt)
		if (din_valid) incnt <= incnt + 32'h1;
	`reg_end(incnt)

	`reg_begin(outdata)
		if (dout_valid) outdata <= dout;
	`reg_end(outdata)
	`reg_begin(outcnt)
		if (dout_valid) outcnt <= outcnt + 32'h1;
	`reg_end(outcnt)
	
*/
