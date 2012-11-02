
`ifdef TEST_DPR_ISOLATION

	initial begin
		#1
		ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_ISOLATION");
		ovm_top.set_report_verbosity_level_hier(OVM_HIGH);
		#60_000 $finish();
	end
	
	/* producer thread: producer -> core */
	initial begin
		#10_000

		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha4a5a6a7);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha0a1a2a3);
		end join_none
		
		#10_000
		
		fork begin
			#(80*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hb0b1b2b3);
			#(10*`ONE_CYCLE_DELAY) pc_0.produce_data(32'hb4b5b6b7);
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
		end join_none
		
		#10_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'he0e1e2e3);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'he4e5e6e7);
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
		#20_000

		fork begin
			
			// Typical isolation scenario 1:
			//
			// During reconfiguration, the producer/consumer request for data transfer with
			// the RM. This request is repeatedly cancelled by the isolator until the 
			// reconfiguration finishes. 
			
			mgr_0.reconfigure_module(8'b0000_0001, `RM_1_ADDR, (`RM_1_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
		#20_000
		
		fork begin
			
			// Typical isolation scenario 2:
			// 
			// The manager requests for partial reconfiguration and the producer/consumer requests 
			// for data transfer at the same time. The RM acknowledges reconfiguration just 
			// before data transfer. As a result, producer/consumer delays the transfer until 
			// the end of reconfiguration and the data is transferred to the new RM. 
			
			mgr_0.reconfigure_module(8'b0000_0000, `RM_0_ADDR, (`RM_0_SIZE+`SBT_HEADER_SIZE));
		end join_none

	end
	
`endif
