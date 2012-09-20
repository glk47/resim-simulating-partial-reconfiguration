
`ifdef TEST_DPR_QUICK_START

	initial begin
		#1
		ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_QUICK_START");
		ovm_top.set_report_verbosity_level_hier(OVM_FULL);
		#80_000 $finish();
	end
	
	/* producer thread: producer -> core */
	initial begin
		#10_000

		fork begin
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha4a5a6a7);
			#(1*`ONE_CYCLE_DELAY) pc_0.produce_data(32'ha0a1a2a3);
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

/*

# ----------------------------------------------------------------
# OVM-2.1.1
# (C) 2007-2009 Mentor Graphics Corporation
# (C) 2007-2009 Cadence Design Systems, Inc.
# ----------------------------------------------------------------
# OVM_INFO @ 0.000ns: reporter [XDRS] Running test: TEST_DPR_QUICK_START
# OVM_INFO @ 0.001ns: reporter [RNTST] Running test ...
# OVM_WARNING D:/My_Designs/UNSW_DRS/dynSim/resim/src/rsv_scoreboard.svh(74) @ 0.001ns: solyr.scb [ReSim] Using the default scoreboard
# OVM_WARNING D:/My_Designs/UNSW_DRS/dynSim/resim/src/rsv_monitor.svh(98) @ 0.001ns: solyr.rr0.mon [ReSim] Using the default monitor
# OVM_WARNING D:/My_Designs/UNSW_DRS/dynSim/resim/src/rsv_monitor.svh(102) @ 0.001ns: solyr.rr0.mon [ReSim] Using the default monitor
# OVM_WARNING D:/My_Designs/UNSW_DRS/dynSim/resim/src/rsv_error_injector.svh(93) @ 0.001ns: solyr.rr0.ei [ReSim] Using the default error injector
# OVM_WARNING D:/My_Designs/UNSW_DRS/dynSim/resim/src/rsv_error_injector.svh(97) @ 0.001ns: solyr.rr0.ei [ReSim] Using the default error injector
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm1 
# OVM_INFO @ 10035.000ns: reporter [PRODUCER] Producing the 0th data: 0xa4a5a6a7
# OVM_INFO @ 10055.000ns: reporter [PRODUCER] Producing the 1th data: 0xa0a1a2a3
# OVM_INFO @ 10075.000ns: reporter [CONSUMER] Consuming the 0th data: 0xa4a5a6a7
# OVM_INFO @ 20005.000ns: reporter [MANAGER] Reconfigure module: rrid:0 rmid:1
# OVM_INFO @ 20115.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 20110.000ns] SBT_OP::SYNC
# OVM_INFO @ 20745.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 20670.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x01, module= my_region.reverse
# [SKT] Reconfigurable Module swapped in: /xdrs/region_0/rm1 
# [SKT] Reconfigurable Module swapped out: /xdrs/region_0/rm0 
# OVM_INFO @ 20815.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 20810.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x0, cdata= 0xf14e5805
# OVM_INFO @ 20885.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 20880.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 20955.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 20950.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21025.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21020.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21095.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21090.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x0, cdata= 0xd3e5923f
# OVM_INFO @ 21165.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21160.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 21235.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21230.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21305.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21300.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21375.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21370.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x0, cdata= 0x6cfd624f
# OVM_INFO @ 21445.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21440.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 21515.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21510.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21585.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21580.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21655.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21650.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x0, cdata= 0x40be81a6
# OVM_INFO @ 21725.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21720.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 21795.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21790.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21865.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21860.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21865.000ns: solyr.cp [ReSim] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 22145.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 22070.000ns] SBT_OP::DESYNC
# OVM_INFO @ 22335.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 30035.000ns: reporter [PRODUCER] Producing the 2th data: 0xb0b1b2b3
# OVM_INFO @ 30055.000ns: reporter [PRODUCER] Producing the 3th data: 0xb4b5b6b7
# OVM_INFO @ 30075.000ns: reporter [CONSUMER] Consuming the 1th data: 0xb4b5b6b7
# OVM_INFO @ 30135.000ns: reporter [CONSUMER] Consuming the 2th data: 0xb0b1b2b3
# OVM_INFO @ 40035.000ns: reporter [PRODUCER] Producing the 4th data: 0xc0c1c2c3
# OVM_INFO @ 40045.000ns: reporter [MANAGER] Reconfigure module: rrid:0 rmid:0
# OVM_INFO @ 40055.000ns: reporter [PRODUCER] Producing the 5th data: 0xc4c5c6c7
# OVM_INFO @ 40075.000ns: reporter [CONSUMER] Consuming the 3th data: 0xc4c5c6c7
# OVM_INFO @ 40135.000ns: reporter [CONSUMER] Consuming the 4th data: 0xc0c1c2c3
# OVM_INFO @ 40235.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 40230.000ns] SBT_OP::SYNC
# OVM_INFO @ 40865.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 40790.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x00, module= my_region.maximum
# [SKT] Reconfigurable Module swapped out: /xdrs/region_0/rm1 
# [SKT] Reconfigurable Module swapped in: /xdrs/region_0/rm0 
# OVM_INFO @ 40935.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 40930.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x0, cdata= 0xa7c438d3
# OVM_INFO @ 41005.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41000.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41075.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41070.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41145.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41140.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41215.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41210.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x0, cdata= 0xdf757d21
# OVM_INFO @ 41285.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41280.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41355.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41350.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41425.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41420.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41495.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41490.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x0, cdata= 0x23ae87f7
# OVM_INFO @ 41565.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41560.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41635.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41630.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41705.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41700.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41775.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41770.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x0, cdata= 0xa7e4733e
# OVM_INFO @ 41845.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41840.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41915.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41910.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41985.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41980.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41985.000ns: solyr.cp [ReSim] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 42265.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 42190.000ns] SBT_OP::DESYNC
# OVM_INFO @ 42455.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 50035.000ns: reporter [PRODUCER] Producing the 6th data: 0xd0d1d2d3
# OVM_INFO @ 50055.000ns: reporter [PRODUCER] Producing the 7th data: 0xd4d5d6d7
# OVM_INFO @ 50075.000ns: reporter [CONSUMER] Consuming the 5th data: 0xd4d5d6d7
# OVM_INFO @ 60005.000ns: reporter [MANAGER] Reconfigure module: rrid:0 rmid:1
# OVM_INFO @ 60115.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 60110.000ns] SBT_OP::SYNC
# OVM_INFO @ 60745.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 60670.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x01, module= my_region.reverse
# [SKT] Reconfigurable Module swapped in: /xdrs/region_0/rm1 
# [SKT] Reconfigurable Module swapped out: /xdrs/region_0/rm0 
# OVM_INFO @ 60815.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 60810.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x0, cdata= 0xf14e5805
# OVM_INFO @ 60885.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 60880.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 60955.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 60950.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 61025.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61020.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 61095.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61090.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x0, cdata= 0xd3e5923f
# OVM_INFO @ 61165.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61160.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 61235.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61230.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 61305.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61300.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 61375.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61370.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x0, cdata= 0x6cfd624f
# OVM_INFO @ 61445.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61440.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 61515.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61510.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 61585.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61580.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 61655.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61650.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x0, cdata= 0x40be81a6
# OVM_INFO @ 61705.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x0 : 0x76543210
# OVM_INFO @ 61765.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x4 : 0xfedcba98
# OVM_INFO @ 61825.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x8 : 0xc001f00d
# OVM_INFO @ 61885.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0xc : 0xdeadbeef
# OVM_INFO @ 61955.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61950.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 62025.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62020.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 62095.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62090.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 62095.000ns: solyr.cp [ReSim] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 62375.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62300.000ns] SBT_OP::DESYNC
# OVM_INFO @ 62565.000ns: reporter [MANAGER] Reconfiguration DONE
# Break in Module xdrs at ./xtests/tdpr_quick_start.sv line 6
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm1 

*/
