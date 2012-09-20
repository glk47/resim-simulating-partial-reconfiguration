
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

/*

# ----------------------------------------------------------------
# OVM-2.1.1
# (C) 2007-2009 Mentor Graphics Corporation
# (C) 2007-2009 Cadence Design Systems, Inc.
# ----------------------------------------------------------------
# OVM_INFO @ 0: reporter [XDRS] Running test: TEST_DPR_ISOLATION
# OVM_INFO @ 1: reporter [RNTST] Running test ...
# OVM_INFO @ 5.000ns: reporter [SCB] [DURING_PH @ 5.000ns] USR_OP::ErrInjection, Starting X Injection
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm1 
# OVM_INFO @ 10035.000ns: reporter [PRODUCER] Producing the 0th data: 0xa4a5a6a7
# OVM_INFO @ 10055.000ns: reporter [PRODUCER] Producing the 1th data: 0xa0a1a2a3
# OVM_INFO @ 10075.000ns: reporter [CONSUMER] Consuming the 0th data: 0xa4a5a6a7
# OVM_INFO @ 20005.000ns: reporter [MANAGER] Reconfigure module: rrid:0 rmid:1
# OVM_INFO @ 20025.000ns: reporter [SCB] [BEFORE_PH @ 20005.000ns] USR_OP::Unloading, Current module unloaded
# OVM_INFO @ 20115.000ns: reporter [SCB] [DURING_PH @ 20110.000ns] SBT_OP::SYNC
# OVM_INFO @ 20745.000ns: reporter [SCB] [DURING_PH @ 20670.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x01, module= my_region.reverse
# [SKT] Reconfigurable Module swapped in: /xdrs/region_0/rm1 
# [SKT] Reconfigurable Module swapped out: /xdrs/region_0/rm0 
# OVM_INFO @ 20815.000ns: reporter [SCB] [DURING_PH @ 20810.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x0, cdata= 0x1409845a
# OVM_INFO @ 20885.000ns: reporter [SCB] [DURING_PH @ 20880.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 20955.000ns: reporter [SCB] [DURING_PH @ 20950.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21025.000ns: reporter [SCB] [DURING_PH @ 21020.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21095.000ns: reporter [SCB] [DURING_PH @ 21090.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x0, cdata= 0x44d9243b
# OVM_INFO @ 21165.000ns: reporter [SCB] [DURING_PH @ 21160.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 21235.000ns: reporter [SCB] [DURING_PH @ 21230.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21305.000ns: reporter [SCB] [DURING_PH @ 21300.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21375.000ns: reporter [SCB] [DURING_PH @ 21370.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x0, cdata= 0xa31a0ff1
# OVM_INFO @ 21445.000ns: reporter [SCB] [DURING_PH @ 21440.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 21515.000ns: reporter [SCB] [DURING_PH @ 21510.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21585.000ns: reporter [SCB] [DURING_PH @ 21580.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21655.000ns: reporter [SCB] [DURING_PH @ 21650.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x0, cdata= 0xaa27e98a
# OVM_INFO @ 21725.000ns: reporter [SCB] [DURING_PH @ 21720.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 21795.000ns: reporter [SCB] [DURING_PH @ 21790.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21865.000ns: reporter [SCB] [DURING_PH @ 21860.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21865.000ns: reporter [ICAP] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 22145.000ns: reporter [SCB] [DURING_PH @ 22070.000ns] SBT_OP::DESYNC
# OVM_INFO @ 22335.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 22335.000ns: reporter [SCB] [AFTER_PH @ 22295.000ns] USR_OP::Activating, New module activated
# OVM_INFO @ 22525.000ns: reporter [PRODUCER] Producing the 2th data: 0xb0b1b2b3
# OVM_INFO @ 22635.000ns: reporter [PRODUCER] Producing the 3th data: 0xb4b5b6b7
# OVM_INFO @ 22655.000ns: reporter [CONSUMER] Consuming the 1th data: 0xb4b5b6b7
# OVM_INFO @ 22715.000ns: reporter [CONSUMER] Consuming the 2th data: 0xb0b1b2b3
# OVM_INFO @ 30035.000ns: reporter [PRODUCER] Producing the 4th data: 0xc0c1c2c3
# OVM_INFO @ 30055.000ns: reporter [PRODUCER] Producing the 5th data: 0xc4c5c6c7
# OVM_INFO @ 30075.000ns: reporter [CONSUMER] Consuming the 3th data: 0xc4c5c6c7
# OVM_INFO @ 30135.000ns: reporter [CONSUMER] Consuming the 4th data: 0xc0c1c2c3
# OVM_INFO @ 40005.000ns: reporter [MANAGER] Reconfigure module: rrid:0 rmid:0
# OVM_INFO @ 40025.000ns: reporter [SCB] [BEFORE_PH @ 40005.000ns] USR_OP::Unloading, Current module unloaded
# OVM_INFO @ 40115.000ns: reporter [SCB] [DURING_PH @ 40110.000ns] SBT_OP::SYNC
# OVM_INFO @ 40745.000ns: reporter [SCB] [DURING_PH @ 40670.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x00, module= my_region.maximum
# [SKT] Reconfigurable Module swapped out: /xdrs/region_0/rm1 
# [SKT] Reconfigurable Module swapped in: /xdrs/region_0/rm0 
# OVM_INFO @ 40815.000ns: reporter [SCB] [DURING_PH @ 40810.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x0, cdata= 0xedb67fb7
# OVM_INFO @ 40885.000ns: reporter [SCB] [DURING_PH @ 40880.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 40955.000ns: reporter [SCB] [DURING_PH @ 40950.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41025.000ns: reporter [SCB] [DURING_PH @ 41020.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41095.000ns: reporter [SCB] [DURING_PH @ 41090.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x0, cdata= 0xd4be1d7b
# OVM_INFO @ 41165.000ns: reporter [SCB] [DURING_PH @ 41160.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41235.000ns: reporter [SCB] [DURING_PH @ 41230.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41305.000ns: reporter [SCB] [DURING_PH @ 41300.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41375.000ns: reporter [SCB] [DURING_PH @ 41370.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x0, cdata= 0x79d2f4df
# OVM_INFO @ 41445.000ns: reporter [SCB] [DURING_PH @ 41440.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41515.000ns: reporter [SCB] [DURING_PH @ 41510.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41585.000ns: reporter [SCB] [DURING_PH @ 41580.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41655.000ns: reporter [SCB] [DURING_PH @ 41650.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x0, cdata= 0x7eaf2e1f
# OVM_INFO @ 41725.000ns: reporter [SCB] [DURING_PH @ 41720.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41795.000ns: reporter [SCB] [DURING_PH @ 41790.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41865.000ns: reporter [SCB] [DURING_PH @ 41860.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41865.000ns: reporter [ICAP] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 42145.000ns: reporter [SCB] [DURING_PH @ 42070.000ns] SBT_OP::DESYNC
# OVM_INFO @ 42335.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 42335.000ns: reporter [SCB] [AFTER_PH @ 42295.000ns] USR_OP::Activating, New module activated
# OVM_INFO @ 42425.000ns: reporter [PRODUCER] Producing the 6th data: 0xd0d1d2d3
# OVM_INFO @ 42445.000ns: reporter [PRODUCER] Producing the 7th data: 0xd4d5d6d7
# OVM_INFO @ 42465.000ns: reporter [CONSUMER] Consuming the 5th data: 0xd4d5d6d7
# OVM_INFO @ 50035.000ns: reporter [PRODUCER] Producing the 8th data: 0xe0e1e2e3
# OVM_INFO @ 50055.000ns: reporter [PRODUCER] Producing the 9th data: 0xe4e5e6e7
# OVM_INFO @ 50075.000ns: reporter [CONSUMER] Consuming the 6th data: 0xe4e5e6e7
# Break in Module xdrs at ./xtests/tdpr_isolation.sv line 6
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm1 

*/
