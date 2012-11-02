
`ifdef TEST_DPR_READBACK

	initial begin
		#1
		ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_READBACK");
		ovm_top.set_report_verbosity_level_hier(OVM_HIGH);
		#60_000 $finish();
	end
	
	/* producer thread: producer -> core */
	initial begin
		#8_000

		fork begin
			#(4*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha4a5a6a7);
			#(4*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha0a1a2a3);
		end join_none
		
		#10_000
		
		fork begin
			#(4*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hb0b1b2b3);
			#(4*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hb4b5b6b7);
		end join_none

		#20_000
		
		fork begin
			#(4*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hc0c1c2c3);
			#(4*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hc4c5c6c7);
		end join_none
		
	end

	/* consumer thread: core -> consumer */
	initial begin
		logic [31:0] data;

		#5_000

		forever begin
			#(4*`ONE_CYCLE_DELAY) pc_0.consume_data(data);
		end

	end

	/* reconfiguration manager thread: reconfigure modules */
	initial begin
		#10_000

		fork begin
			
			// GCAPTURE and and then readback. You can view the state data 
			// from the simulation-only bitstream returned from the ICAP.
			
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_GCAPTURE_SEQ, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_RD_RM_0_HEADER, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_RCFG, `DMA_BUFFER, `RM_0_SIZE);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_DESYNC_SEQ, 12);
			
			// Change the readback data
			
			pc_0.write_data(`DMA_BUFFER+1, 32'h88442211);
			pc_0.write_data(`DMA_BUFFER+2, 32'hff117733);
			pc_0.write_data(`DMA_BUFFER+6, 32'hc3c3a5a5);
			pc_0.write_data(`DMA_BUFFER+7, 32'h1f1f2e2e);
			
		end join_none

		#10_000
		fork begin
			
			// Setup a mask and then restore state, the state data 
			// should be masked. 
			
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_WR_MSK_1_SEQ, 12);

			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_WR_RM_0_HEADER, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_BUFFER, `RM_0_SIZE);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_GRESTORE_SEQ, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_DESYNC_SEQ, 12);
		end join_none

		#10_000
		fork begin
			
			// Clear the mask and issue a GRESTORE command. The state data
			// should be copied to the RM. In particular, as the FSM registers are restored
			// to and none-idle state, the RM starts state data processing immediately 
			// after restoration without any requests from the producer/consumer
			
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_WR_MSK_0_SEQ, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_GRESTORE_SEQ, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_DESYNC_SEQ, 12);
		end join_none

		#10_000
		fork begin
			
			// A typical restoration flow: 
			// 
			//    open mask -> stop clock -> GCAPTURE -> readback one frame -> change the state data 
			//    -> write one frame -> GRESTORE -> resume clock -> close mask
			//
			// The static part must (1) stop the clock so as to keep the RM frozen in the  
			// saving/restoring process, (2) GCAPTURE and readback before restoration so that one
			// the state data in the frame of interest is changed.
			
			// 1. open mask, 2. stop clock, 3. GCAPTURE
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_WR_MSK_0_SEQ, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.set_rc_clock_en(4'b1110);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_GCAPTURE_SEQ, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_DESYNC_SEQ, 12);
			
			// 4. readback one frame
			pc_0.write_data(`DMA_RD_RM_0_HEADER+7, 32'h00000001);  // the frame_address of SBT
			pc_0.write_data(`DMA_RD_RM_0_HEADER+11, 32'h50000004); // the size field of SBT
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_RD_RM_0_HEADER, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_RCFG, `DMA_BUFFER, 4);
			
			// 5. change the state data
			pc_0.write_data(`DMA_BUFFER+1, 32'hfedcba98);
			pc_0.write_data(`DMA_BUFFER+2, 32'h76543210);
			
			// 6. write one frame
			pc_0.write_data(`DMA_WR_RM_0_HEADER+7, 32'h00000001);  // the frame_address of SBT
			pc_0.write_data(`DMA_WR_RM_0_HEADER+11, 32'h50000004); // the size field of SBT
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_WR_RM_0_HEADER, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_BUFFER, 4);
			
			// 7. GRESTORE, 8. resume clock, 9. close mask
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_GRESTORE_SEQ, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.set_rc_clock_en(4'b1111);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_WR_MSK_1_SEQ, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_DESYNC_SEQ, 12);
		end join_none
		
	end
	
`endif
