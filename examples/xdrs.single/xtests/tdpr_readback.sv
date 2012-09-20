
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

/*

# ----------------------------------------------------------------
# OVM-2.1.1
# (C) 2007-2009 Mentor Graphics Corporation
# (C) 2007-2009 Cadence Design Systems, Inc.
# ----------------------------------------------------------------
# OVM_INFO @ 0: reporter [XDRS] Running test: TEST_DPR_READBACK
# OVM_INFO @ 1: reporter [RNTST] Running test ...
# OVM_INFO @ 5.000ns: reporter [SCB] [DURING_PH @ 5.000ns] USR_OP::ErrInjection, Starting X Injection
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm1 
# OVM_INFO @ 8065.000ns: reporter [PRODUCER] Producing the 0th data: 0xa4a5a6a7
# OVM_INFO @ 8115.000ns: reporter [PRODUCER] Producing the 1th data: 0xa0a1a2a3
# OVM_INFO @ 8135.000ns: reporter [CONSUMER] Consuming the 0th data: 0xa4a5a6a7
# OVM_INFO @ 10025.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x520 s:0xc
# OVM_INFO @ 10095.000ns: reporter [SCB] [DURING_PH @ 10090.000ns] SBT_OP::SYNC
# [SKT] Invoking gcapture thread: rsv_gcapture_hdl_state /xdrs/region_0 rm0 
# OVM_INFO @ 10725.116ns: reporter [SCB] [DURING_PH @ 10650.000ns] SBT_OP::GCAPTURE, rrid= 0x00
# OVM_INFO @ 10875.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 10895.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x420 s:0xc
# OVM_INFO @ 11735.000ns: reporter [SCB] [DURING_PH @ 11660.000ns] SBT_OP::RCFG, rrid= 0x00, rmid= 0x00, module= my_region.maximum
# OVM_INFO @ 11745.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 11765.000ns: reporter [MANAGER] Read ICAP (DMA): a:0x800 s:0x10
# OVM_INFO @ 11795.000ns: reporter [SCB] [DURING_PH @ 11790.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x0, cdata= 0xedb67fb7
# OVM_INFO @ 11875.000ns: reporter [SCB] [DURING_PH @ 11870.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x1, cdata= 0xa4a5a6a7
# OVM_INFO @ 11955.000ns: reporter [SCB] [DURING_PH @ 11950.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x2, cdata= 0x0a1a2a3f
# OVM_INFO @ 12035.000ns: reporter [SCB] [DURING_PH @ 12030.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x3, cdata= 0x0000000a
# OVM_INFO @ 12115.000ns: reporter [SCB] [DURING_PH @ 12110.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x0, cdata= 0xd4be1d7b
# OVM_INFO @ 12195.000ns: reporter [SCB] [DURING_PH @ 12190.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x1, cdata= 0xa4a5a6a7
# OVM_INFO @ 12275.000ns: reporter [SCB] [DURING_PH @ 12270.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x2, cdata= 0x00000001
# OVM_INFO @ 12355.000ns: reporter [SCB] [DURING_PH @ 12350.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 12435.000ns: reporter [SCB] [DURING_PH @ 12430.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x0, cdata= 0x79d2f4df
# OVM_INFO @ 12515.000ns: reporter [SCB] [DURING_PH @ 12510.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x1, cdata= 0xa0a1a2a3
# OVM_INFO @ 12595.000ns: reporter [SCB] [DURING_PH @ 12590.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x2, cdata= 0x00000002
# OVM_INFO @ 12675.000ns: reporter [SCB] [DURING_PH @ 12670.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 12755.000ns: reporter [SCB] [DURING_PH @ 12750.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x0, cdata= 0x7eaf2e1f
# OVM_INFO @ 12835.000ns: reporter [SCB] [DURING_PH @ 12830.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 12915.000ns: reporter [SCB] [DURING_PH @ 12910.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 12995.000ns: reporter [SCB] [DURING_PH @ 12990.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 12995.000ns: reporter [ICAP] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 13055.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 13075.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x500 s:0xc
# OVM_INFO @ 13775.000ns: reporter [SCB] [DURING_PH @ 13700.000ns] SBT_OP::DESYNC
# OVM_INFO @ 13925.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 13995.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x801 : 0x88442211
# OVM_INFO @ 14065.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x802 : 0xff117733
# OVM_INFO @ 14135.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x806 : 0xc3c3a5a5
# OVM_INFO @ 14205.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x807 : 0x1f1f2e2e
# OVM_INFO @ 18065.000ns: reporter [PRODUCER] Producing the 2th data: 0xb0b1b2b3
# OVM_INFO @ 18115.000ns: reporter [PRODUCER] Producing the 3th data: 0xb4b5b6b7
# OVM_INFO @ 18135.000ns: reporter [CONSUMER] Consuming the 1th data: 0xb4b5b6b7
# OVM_INFO @ 20025.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x560 s:0xc
# OVM_INFO @ 20095.000ns: reporter [SCB] [DURING_PH @ 20090.000ns] SBT_OP::SYNC
# OVM_INFO @ 20585.000ns: reporter [SCB] [DURING_PH @ 20510.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0xff, module= RR0.mask
# OVM_INFO @ 20655.000ns: reporter [SCB] [DURING_PH @ 20650.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x0, cdata= 0x00000000
# OVM_INFO @ 20725.000ns: reporter [SCB] [DURING_PH @ 20720.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 20795.000ns: reporter [SCB] [DURING_PH @ 20790.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 20865.000ns: reporter [SCB] [DURING_PH @ 20860.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x3, cdata= 0x00002000
# OVM_INFO @ 20865.000ns: reporter [ICAP] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 20875.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 20895.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x400 s:0xc
# OVM_INFO @ 21735.000ns: reporter [SCB] [DURING_PH @ 21660.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x00, module= my_region.maximum
# OVM_INFO @ 21745.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 21765.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x800 s:0x10
# OVM_INFO @ 21835.000ns: reporter [SCB] [DURING_PH @ 21830.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x0, cdata= 0xedb67fb7
# OVM_INFO @ 21905.000ns: reporter [SCB] [DURING_PH @ 21900.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x1, cdata= 0x88442211
# OVM_INFO @ 21975.000ns: reporter [SCB] [DURING_PH @ 21970.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x2, cdata= 0xff117733
# OVM_INFO @ 22045.000ns: reporter [SCB] [DURING_PH @ 22040.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x3, cdata= 0x0000000a
# OVM_INFO @ 22115.000ns: reporter [SCB] [DURING_PH @ 22110.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x0, cdata= 0xd4be1d7b
# OVM_INFO @ 22185.000ns: reporter [SCB] [DURING_PH @ 22180.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x1, cdata= 0xa4a5a6a7
# OVM_INFO @ 22255.000ns: reporter [SCB] [DURING_PH @ 22250.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x2, cdata= 0xc3c3a5a5
# OVM_INFO @ 22325.000ns: reporter [SCB] [DURING_PH @ 22320.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x3, cdata= 0x1f1f2e2e
# OVM_INFO @ 22395.000ns: reporter [SCB] [DURING_PH @ 22390.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x0, cdata= 0x79d2f4df
# OVM_INFO @ 22465.000ns: reporter [SCB] [DURING_PH @ 22460.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x1, cdata= 0xa0a1a2a3
# OVM_INFO @ 22535.000ns: reporter [SCB] [DURING_PH @ 22530.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x2, cdata= 0x00000002
# OVM_INFO @ 22605.000ns: reporter [SCB] [DURING_PH @ 22600.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 22675.000ns: reporter [SCB] [DURING_PH @ 22670.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x0, cdata= 0x7eaf2e1f
# OVM_INFO @ 22745.000ns: reporter [SCB] [DURING_PH @ 22740.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 22815.000ns: reporter [SCB] [DURING_PH @ 22810.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 22885.000ns: reporter [SCB] [DURING_PH @ 22880.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 22885.000ns: reporter [ICAP] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 22895.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 22915.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x540 s:0xc
# OVM_INFO @ 23615.000ns: reporter [SCB] [DURING_PH @ 23540.000ns] SBT_OP::GRESTORE, rrid= 0x00
# OVM_INFO @ 23765.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 23785.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x500 s:0xc
# OVM_INFO @ 24485.000ns: reporter [SCB] [DURING_PH @ 24410.000ns] SBT_OP::DESYNC
# OVM_INFO @ 24635.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 30025.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x580 s:0xc
# OVM_INFO @ 30095.000ns: reporter [SCB] [DURING_PH @ 30090.000ns] SBT_OP::SYNC
# OVM_INFO @ 30585.000ns: reporter [SCB] [DURING_PH @ 30510.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0xff, module= RR0.mask
# OVM_INFO @ 30655.000ns: reporter [SCB] [DURING_PH @ 30650.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x0, cdata= 0x00000000
# OVM_INFO @ 30725.000ns: reporter [SCB] [DURING_PH @ 30720.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 30795.000ns: reporter [SCB] [DURING_PH @ 30790.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 30865.000ns: reporter [SCB] [DURING_PH @ 30860.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 30865.000ns: reporter [ICAP] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 30875.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 30895.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x540 s:0xc
# [SKT] Invoking grestore thread: rsv_grestore_hdl_state /xdrs/region_0 rm0 
# OVM_INFO @ 31595.116ns: reporter [SCB] [DURING_PH @ 31520.000ns] SBT_OP::GRESTORE, rrid= 0x00
# OVM_INFO @ 31745.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 31765.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x500 s:0xc
# OVM_INFO @ 31775.000ns: reporter [CONSUMER] Consuming the 2th data: 0xaff11773
# OVM_INFO @ 32465.000ns: reporter [SCB] [DURING_PH @ 32390.000ns] SBT_OP::DESYNC
# OVM_INFO @ 32615.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 38065.000ns: reporter [PRODUCER] Producing the 4th data: 0xc0c1c2c3
# OVM_INFO @ 38115.000ns: reporter [PRODUCER] Producing the 5th data: 0xc4c5c6c7
# OVM_INFO @ 38135.000ns: reporter [CONSUMER] Consuming the 3th data: 0xc4c5c6c7
# OVM_INFO @ 40025.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x580 s:0xc
# OVM_INFO @ 40095.000ns: reporter [SCB] [DURING_PH @ 40090.000ns] SBT_OP::SYNC
# OVM_INFO @ 40585.000ns: reporter [SCB] [DURING_PH @ 40510.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0xff, module= RR0.mask
# OVM_INFO @ 40655.000ns: reporter [SCB] [DURING_PH @ 40650.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x0, cdata= 0x00000000
# OVM_INFO @ 40725.000ns: reporter [SCB] [DURING_PH @ 40720.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 40795.000ns: reporter [SCB] [DURING_PH @ 40790.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 40865.000ns: reporter [SCB] [DURING_PH @ 40860.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 40865.000ns: reporter [ICAP] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 40875.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 40905.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x520 s:0xc
# [SKT] Invoking gcapture thread: rsv_gcapture_hdl_state /xdrs/region_0 rm0 
# OVM_INFO @ 41605.116ns: reporter [SCB] [DURING_PH @ 41530.000ns] SBT_OP::GCAPTURE, rrid= 0x00
# OVM_INFO @ 41755.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 41775.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x500 s:0xc
# OVM_INFO @ 42475.000ns: reporter [SCB] [DURING_PH @ 42400.000ns] SBT_OP::DESYNC
# OVM_INFO @ 42625.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 42695.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x427 : 0x00000001
# OVM_INFO @ 42765.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x42b : 0x50000004
# OVM_INFO @ 42785.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x420 s:0xc
# OVM_INFO @ 42855.000ns: reporter [SCB] [DURING_PH @ 42850.000ns] SBT_OP::SYNC
# OVM_INFO @ 43625.000ns: reporter [SCB] [DURING_PH @ 43550.000ns] SBT_OP::RCFG, rrid= 0x00, rmid= 0x00, module= my_region.maximum
# OVM_INFO @ 43635.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 43655.000ns: reporter [MANAGER] Read ICAP (DMA): a:0x800 s:0x4
# OVM_INFO @ 43685.000ns: reporter [SCB] [DURING_PH @ 43680.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x0, cdata= 0xd4be1d7b
# OVM_INFO @ 43765.000ns: reporter [SCB] [DURING_PH @ 43760.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x1, cdata= 0xc4c5c6c7
# OVM_INFO @ 43845.000ns: reporter [SCB] [DURING_PH @ 43840.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x2, cdata= 0xc3c3a5a7
# OVM_INFO @ 43925.000ns: reporter [SCB] [DURING_PH @ 43920.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x3, cdata= 0x1f1f2e2e
# OVM_INFO @ 43985.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 44055.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x801 : 0xfedcba98
# OVM_INFO @ 44125.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x802 : 0x76543210
# OVM_INFO @ 44195.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x407 : 0x00000001
# OVM_INFO @ 44265.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x40b : 0x50000004
# OVM_INFO @ 44285.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x400 s:0xc
# OVM_INFO @ 45125.000ns: reporter [SCB] [DURING_PH @ 45050.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x00, module= my_region.maximum
# OVM_INFO @ 45135.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 45155.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x800 s:0x4
# OVM_INFO @ 45225.000ns: reporter [SCB] [DURING_PH @ 45220.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x0, cdata= 0xd4be1d7b
# OVM_INFO @ 45295.000ns: reporter [SCB] [DURING_PH @ 45290.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x1, cdata= 0xfedcba98
# OVM_INFO @ 45365.000ns: reporter [SCB] [DURING_PH @ 45360.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x2, cdata= 0x76543210
# OVM_INFO @ 45435.000ns: reporter [SCB] [DURING_PH @ 45430.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x3, cdata= 0x1f1f2e2e
# OVM_INFO @ 45445.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 45465.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x540 s:0xc
# [SKT] Invoking grestore thread: rsv_grestore_hdl_state /xdrs/region_0 rm0 
# OVM_INFO @ 46165.116ns: reporter [SCB] [DURING_PH @ 46090.000ns] SBT_OP::GRESTORE, rrid= 0x00
# OVM_INFO @ 46315.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 46345.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x560 s:0xc
# OVM_INFO @ 46905.000ns: reporter [SCB] [DURING_PH @ 46830.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0xff, module= RR0.mask
# OVM_INFO @ 46975.000ns: reporter [SCB] [DURING_PH @ 46970.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x0, cdata= 0x00000000
# OVM_INFO @ 47045.000ns: reporter [SCB] [DURING_PH @ 47040.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 47115.000ns: reporter [SCB] [DURING_PH @ 47110.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 47185.000ns: reporter [SCB] [DURING_PH @ 47180.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0xff, mna= 0x0000, wofft= 0x3, cdata= 0x00002000
# OVM_INFO @ 47185.000ns: reporter [ICAP] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 47195.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 47215.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x500 s:0xc
# OVM_INFO @ 47915.000ns: reporter [SCB] [DURING_PH @ 47840.000ns] SBT_OP::DESYNC
# OVM_INFO @ 48065.000ns: reporter [MANAGER] Read/Write ICAP DONE
# Break in Module xdrs at ./xtests/tdpr_readback.sv line 6
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm1 

*/
