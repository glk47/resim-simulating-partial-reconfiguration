
`ifdef TEST_DPR_SIMPLE

	initial begin
		#1
		ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_SIMPLE");
		ovm_top.set_report_verbosity_level_hier(OVM_HIGH);
		#80_000 $finish();
	end
	
	/* producer thread: producer -> core */
	initial begin
		#10_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha0a1a2a3);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha0a1a2a3);
			
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha4a5a6a7);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha4a5a6a7);
		end join_none
		
		#20_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hb0b1b2b3);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hb4b5b6b7);
		end join_none

		#10_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hc0c1c2c3);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hc4c5c6c7);
		end join_none
		
		#10_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hd0d1d2d3);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hd4d5d6d7);
			
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hd2d3d0d1);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hd6d7d4d5);
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

		#60_000

		fork begin
			#1_600
			
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
			
			// Partial Reconfiguration when the RM is idle
			
			mgr_0.reconfigure_module(8'b0000_0001, `RM_1_ADDR, (`RM_1_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
		#20_000
		
		fork begin
			
			// Partial Reconfiguration when the RM is busy, reconfiguration
			// is delayed until the RM finished processing the current data
			
			#(4*`ONE_CYCLE_DELAY) mgr_0.reconfigure_module(8'b0000_0000, `RM_0_ADDR, (`RM_0_SIZE+`SBT_HEADER_SIZE));
		end join_none

		#20_000

		fork begin
			
			// Partial Reconfiguration with a dummy memory traffic 
			// the bus pauses the bitstream traffic and let the dummy memory traffic finishes
			// before resuming the transfer of the simulation-only bitstream
			
			mgr_0.reconfigure_module(8'b0000_0001, `RM_1_ADDR, (`RM_1_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
	end
	
`endif
