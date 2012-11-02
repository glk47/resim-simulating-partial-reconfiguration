
`ifdef TEST_DPR_RANDOM

	initial begin
		#1
		ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_RANDOM");
		ovm_top.set_report_verbosity_level_hier(OVM_MEDIUM);
		#800_000 $finish();
	end
	
	/* producer thread: producer -> core */
	initial begin
		#10_000

		forever begin
			#(($urandom()%128)*`ONE_CYCLE_DELAY)
			
			repeat (2+$urandom()%4) 
				#(($urandom()%16)*`ONE_CYCLE_DELAY) pc_0.produce_data($urandom());
		end
		
	end

	/* consumer thread: core -> consumer */
	initial begin
		logic [31:0] data;

		#5_000

		forever begin
			#(($urandom()%8)*`ONE_CYCLE_DELAY) pc_0.consume_data(data, $urandom()%4);
		end

	end

	/* dummy memory traffic (dmt) thread */
	initial begin
		#10_000

		forever begin
			#(($urandom()%128)*`ONE_CYCLE_DELAY)
			
			repeat (2+$urandom()%4) 
				#(($urandom()%16)*`ONE_CYCLE_DELAY) pc_0.write_data(32'h0, $urandom());
		end

	end
	
	/* reconfiguration manager thread: reconfigure modules */
	initial begin
		
		forever begin
			#((1024+$urandom()%1024)*`ONE_CYCLE_DELAY) mgr_0.reconfigure_module(8'b0000_0001, `RM_1_ADDR, (`RM_1_SIZE+`SBT_HEADER_SIZE));
			#((1024+$urandom()%1024)*`ONE_CYCLE_DELAY) mgr_0.reconfigure_module(8'b0000_0000, `RM_0_ADDR, (`RM_0_SIZE+`SBT_HEADER_SIZE));
		end
		
	end
	
`endif
