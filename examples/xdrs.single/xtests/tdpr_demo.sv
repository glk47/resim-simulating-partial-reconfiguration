
`ifdef TEST_DPR_DEMO

	initial begin
		#1
		ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_DEMO");
		ovm_top.set_report_verbosity_level_hier(OVM_HIGH);
		#80_000 $finish();
	end
	
	/* producer thread: producer -> core */
	initial begin
		#20_000

		fork begin 
			
			// This computaion delays start of the reconfiguration.
			// It arrives just before the request of reconfiguration.
			
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hcafeface);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hcafefacd);
		end join_none
		
		#10_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'h1eaffa11);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'h1eaff001);
		end join_none

		#10_000
		
		fork begin 
			
			// This computaion is initiated during reconfiguration,
			// and the static module keep retrying until the RM 
			// is reconfigured. 
			
			
			#(80*`ONE_CYCLE_DELAY) pc_0.produce_data(32'h1eaffa11);
			#(80*`ONE_CYCLE_DELAY) pc_0.produce_data(32'h1eaff001);
		end join_none
		
		#10_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'h1eaffa11);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'h1eaff001);
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

	/* dummy memory traffic (dmt) thread */
	initial begin
		logic [31:0] data;

		#20_000

		fork begin
			#1_000
			
			// The following memory transfers has a higher priority than the 
			// bitstream traffic. Therefore, bitstream transfer was delayed 
			// until these memory transfers finishes. 
			
			pc_0.write_data(32'h0, 32'h76543210);
			pc_0.write_data(32'h4, 32'hfedcba98);

			pc_0.write_data(32'h8, 32'hc001f00d);
			pc_0.write_data(32'hc, 32'hdeadbeef);
		end join_none

	end

	/* reconfiguration manager thread: reconfigure modules */
	initial begin
		#20_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) mgr_0.reconfigure_module(8'b0000_0001, `RM_1_ADDR, (`RM_1_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
		#20_000
		
		fork begin
			#(0*`ONE_CYCLE_DELAY) mgr_0.reconfigure_module(8'b0000_0000, `RM_0_ADDR, (`RM_0_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
		#20_000

		fork begin
			
			// GCAPTURE and and then readback. You can view the state data 
			// from the simulation-only bitstream returned from the ICAP.
			
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_GCAPTURE_SEQ, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_RD_RM_0_HEADER, 12);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_RCFG, `DMA_BUFFER, `RM_0_SIZE);
			#(1*`ONE_CYCLE_DELAY) mgr_0.icap_dma_bitstream(`DMA_WCFG, `DMA_DESYNC_SEQ, 12);
		end join_none
			
	end
	
`endif
