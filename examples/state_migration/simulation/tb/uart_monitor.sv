//---------------------------------------------------------------------
//
// Company:  UNSW
// Original Author: Lingkan Gong
// Project Name: XPCIe
//
// Create Date:    01/03/2012
// Design Name:    uart_monitor
//
//---------------------------------------------------------------------

`timescale 1ns/1ps

module uart_monitor #(parameter
	C_UART_ID = 0,
	C_CLK_FREQ_HZ = 100000000,
	C_BAUDRATE = 1000000,
	C_DATA_BITS = 8,
	C_USE_PARITY = 0,
	C_ODD_PARITY = 0
)
(
	input                 clk           ,
	input                 rstn          ,

	input                 rx            ,
	output logic          tx            

);
	integer C_CHAR_DELAY;
	integer C_RATIO;
	function integer calc_ratio;
		integer c_baudrate_16_by_2 = (16 * C_BAUDRATE) / 2;
		integer remainder = C_CLK_FREQ_HZ % (16 * C_BAUDRATE);
		integer ratio = C_CLK_FREQ_HZ / (16 * C_BAUDRATE);
		
		if (c_baudrate_16_by_2 < remainder) ratio = ratio + 1;
		return ratio;
		
	endfunction
	
	initial begin : receive_thread
		wait (rstn == 1'b1);
		C_RATIO = calc_ratio();
		C_CHAR_DELAY = (1000_000_000 / C_CLK_FREQ_HZ) * 16 * C_RATIO;
		
		forever begin
			logic       data[8];
			logic [7:0] uart_char;
			logic       parity;
			
			
			@(posedge clk iff (rx == 1'b0)); // start bit
			
			@(posedge clk);
			@(posedge clk);
			
			for(int i = 0; i< C_DATA_BITS; i++) begin
				
				repeat (16*C_RATIO) @(posedge clk);
				data[i] = rx;
			end
			
			repeat (16*C_RATIO) @(posedge clk);
			if (C_USE_PARITY) begin
				parity = rx;
				repeat (16*C_RATIO) @(posedge clk);;
			end
			
			assert (rx==1'b1); // stop bit
			
			uart_char = {data[7], data[6], data[5], data[4], data[3], data[2], data[1], data[0]};
			if (uart_char > 8'd31 & uart_char < 8'd127) begin
				$display ("[UART %0d @%t] Transmitted: 0x%h(%c)", C_UART_ID, $realtime, uart_char, uart_char);
			end else begin
				$display ("[UART %0d @%t] Transmitted: 0x%h(special char)", C_UART_ID, $realtime, uart_char);
			end
		
		end
	end
	
	assign tx = 1'b1;
	
endmodule
