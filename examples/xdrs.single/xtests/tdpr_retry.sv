
`ifdef TEST_DPR_RETRY

	initial begin
		#1
		ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_RETRY");
		ovm_top.set_report_verbosity_level_hier(OVM_HIGH);
		#60_000 $finish();
	end
	
	/* producer thread: producer -> core */
	initial begin
		#10_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data($urandom());
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data($urandom());
		end join_none
		
		#20_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data($urandom());
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data($urandom());
		end join_none

		#10_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data($urandom());
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data($urandom());
		end join_none
		
		#10_000
		
		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data($urandom());
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data($urandom());
		end join_none
		
	end

	/* consumer thread: core -> consumer */
	initial begin
		logic [31:0] data;

		#5_000

		forever begin
			
			// The consumer thread has "long" delays and the
			// reconfigurable module need to retry the operation. 
			
			#(4*`ONE_CYCLE_DELAY) pc_0.consume_data(data,1);
		end

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
		
	end
	
`endif
