
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
			// and the static module keep retrying until the module 
			// it is communicating with finally finished reconfiguration
			
			
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
	

	/* error injection thread: inject errors when during partial reconfiguration */
	
	my_ei ei;
	
	initial begin
		#40_000
		$cast(ei, ovm_top.find("*.rr0.ei"));
		
		fork begin
			#1_000 
			
			ei.ei_reset_rm();
			ei.ei_inject_to_rm($urandom('hab1e));
		end join_none
	
	end
	
`endif

/*

# ----------------------------------------------------------------
# OVM-2.1.1
# (C) 2007-2009 Mentor Graphics Corporation
# (C) 2007-2009 Cadence Design Systems, Inc.
# ----------------------------------------------------------------
# OVM_INFO @ 0.000ns: reporter [RNTST] Running test ...
# OVM_INFO @ 1.000ns: reporter [XDRS] Running test: TEST_DPR_DEMO
# OVM_INFO @ 5.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 5.000ns] USR_OP::ErrInjection, Starting X Injection
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm1 
# OVM_INFO @ 35.000ns: solyr.rr0.mon [ReSim] [AFTER_PH @ 0.000ns] USR_OP::Activating, New module activated
# OVM_INFO @ 20015.000ns: reporter [MANAGER] Reconfigure module: rrid:0 rmid:1
# OVM_INFO @ 20035.000ns: reporter [PRODUCER] Producing the 0th data: 0xba1dba11
# OVM_INFO @ 20055.000ns: reporter [PRODUCER] Producing the 1th data: 0xdeedbeaf
# OVM_INFO @ 20125.000ns: reporter [CONSUMER] Consuming the 0th data: 0xdeedbeaf
# OVM_INFO @ 20135.000ns: solyr.rr0.mon [ReSim] [BEFORE_PH @ 20015.000ns] USR_OP::Unloading, Current module unloaded
# OVM_INFO @ 20225.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 20220.000ns] SBT_OP::SYNC
# OVM_INFO @ 20855.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 20780.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x01, module= my_region.reverse
# [SKT] Reconfigurable Module swapped in: /xdrs/region_0/rm1 
# [SKT] Reconfigurable Module swapped out: /xdrs/region_0/rm0 
# OVM_INFO @ 20905.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x0 : 0x76543210
# OVM_INFO @ 20965.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x4 : 0xfedcba98
# OVM_INFO @ 21025.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0x8 : 0xa5a55a5a
# OVM_INFO @ 21085.000ns: reporter [MEMORYTRAFFIC] Writing data @ 0xc : 0xc4c44c4c
# OVM_INFO @ 21155.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21150.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x0, cdata= 0xc0cd0e4a
# OVM_INFO @ 21225.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21220.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 21295.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21290.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21365.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21360.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0000, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21435.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21430.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x0, cdata= 0x23f9db25
# OVM_INFO @ 21505.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21500.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 21575.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21570.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21645.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21640.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0001, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21715.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21710.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x0, cdata= 0x6b84e3c7
# OVM_INFO @ 21785.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21780.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 21855.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21850.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 21925.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21920.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 21995.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 21990.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x0, cdata= 0x243fdecb
# OVM_INFO @ 22065.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 22060.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 22135.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 22130.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 22205.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 22200.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x01, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 22205.000ns: solyr.cp [ReSim] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 22485.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 22410.000ns] SBT_OP::DESYNC
# OVM_INFO @ 22675.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 22675.000ns: solyr.rr0.mon [ReSim] [AFTER_PH @ 22635.000ns] USR_OP::Activating, New module activated
# OVM_INFO @ 30035.000ns: reporter [PRODUCER] Producing the 2th data: 0xcafeface
# OVM_INFO @ 30055.000ns: reporter [PRODUCER] Producing the 3th data: 0xc001f00d
# OVM_INFO @ 30125.000ns: reporter [CONSUMER] Consuming the 1th data: 0xc001f00d
# OVM_INFO @ 30185.000ns: reporter [CONSUMER] Consuming the 2th data: 0xcafeface
# OVM_INFO @ 40005.000ns: reporter [MANAGER] Reconfigure module: rrid:0 rmid:0
# OVM_INFO @ 40025.000ns: solyr.rr0.mon [ReSim] [BEFORE_PH @ 40005.000ns] USR_OP::Unloading, Current module unloaded
# OVM_INFO @ 40115.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 40110.000ns] SBT_OP::SYNC
# OVM_INFO @ 40745.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 40670.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x00, module= my_region.maximum
# [SKT] Reconfigurable Module swapped out: /xdrs/region_0/rm1 
# [SKT] Reconfigurable Module swapped in: /xdrs/region_0/rm0 
# OVM_INFO @ 40815.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 40810.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x0, cdata= 0xdbfc8e0b
# OVM_INFO @ 40885.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 40880.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 40895.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 40801.000ns] USR_OP::ErrInjection, DEI: Random Injection, data= 0x67670167
# OVM_INFO @ 40955.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 40950.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41025.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41020.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41095.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41090.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x0, cdata= 0x831244cd
# OVM_INFO @ 41165.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41160.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41235.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41230.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41305.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41300.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41375.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41370.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x0, cdata= 0x23992344
# OVM_INFO @ 41445.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41440.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41515.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41510.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41585.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41580.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41655.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41650.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x0, cdata= 0x6a1c6bda
# OVM_INFO @ 41725.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41720.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 41795.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41790.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 41865.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 41860.000ns] SBT_OP::WSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 41865.000ns: solyr.cp [ReSim] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 42145.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 42070.000ns] SBT_OP::DESYNC
# OVM_INFO @ 42335.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 42335.000ns: solyr.rr0.mon [ReSim] [AFTER_PH @ 42295.000ns] USR_OP::Activating, New module activated
# OVM_INFO @ 42525.000ns: reporter [PRODUCER] Producing the 4th data: 0xba1dba11
# OVM_INFO @ 43335.000ns: reporter [PRODUCER] Producing the 5th data: 0xdeedbeaf
# OVM_INFO @ 43385.000ns: reporter [CONSUMER] Consuming the 3th data: 0xdeedbeaf
# OVM_INFO @ 50035.000ns: reporter [PRODUCER] Producing the 6th data: 0xcafeface
# OVM_INFO @ 50055.000ns: reporter [PRODUCER] Producing the 7th data: 0xc001f00d
# OVM_INFO @ 50115.000ns: reporter [CONSUMER] Consuming the 4th data: 0xcafeface
# OVM_INFO @ 60025.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x520 s:0xc
# OVM_INFO @ 60095.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 60090.000ns] SBT_OP::SYNC
# [SKT] Invoking gcapture thread: rsv_gcapture_hdl_state /xdrs/region_0 rm0 
# OVM_INFO @ 60725.116ns: solyr.rr0.mon [ReSim] [DURING_PH @ 60650.000ns] SBT_OP::GCAPTURE, rrid= 0x00
# OVM_INFO @ 60875.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 60895.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x420 s:0xc
# OVM_INFO @ 61735.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61660.000ns] SBT_OP::RCFG, rrid= 0x00, rmid= 0x00, module= my_region.maximum
# OVM_INFO @ 61745.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 61765.000ns: reporter [MANAGER] Read ICAP (DMA): a:0x800 s:0x10
# OVM_INFO @ 61795.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61790.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x0, cdata= 0xdbfc8e0b
# OVM_INFO @ 61875.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61870.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x1, cdata= 0xcafeface
# OVM_INFO @ 61955.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61950.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x2, cdata= 0x001f00df
# OVM_INFO @ 62035.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62030.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0000, wofft= 0x3, cdata= 0x0000000c
# OVM_INFO @ 62115.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62110.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x0, cdata= 0x831244cd
# OVM_INFO @ 62195.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62190.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x1, cdata= 0xcafeface
# OVM_INFO @ 62275.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62270.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x2, cdata= 0x00000002
# OVM_INFO @ 62355.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62350.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0001, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 62435.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62430.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x0, cdata= 0x23992344
# OVM_INFO @ 62515.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62510.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x1, cdata= 0xc001f00d
# OVM_INFO @ 62595.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62590.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x2, cdata= 0x00000004
# OVM_INFO @ 62675.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62670.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0002, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 62755.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62750.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x0, cdata= 0x6a1c6bda
# OVM_INFO @ 62835.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62830.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x1, cdata= 0x00000000
# OVM_INFO @ 62915.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62910.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x2, cdata= 0x00000000
# OVM_INFO @ 62995.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 62990.000ns] SBT_OP::RSPY, rrid= 0x00, rmid= 0x00, mna= 0x0003, wofft= 0x3, cdata= 0x00000000
# OVM_INFO @ 62995.000ns: solyr.cp [ReSim] Configuration reaches end of current Reconfigurable Region
# OVM_INFO @ 63055.000ns: reporter [MANAGER] Read/Write ICAP DONE
# OVM_INFO @ 63075.000ns: reporter [MANAGER] Write ICAP (DMA): a:0x500 s:0xc
# OVM_INFO @ 63775.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 63700.000ns] SBT_OP::DESYNC
# OVM_INFO @ 63925.000ns: reporter [MANAGER] Read/Write ICAP DONE
# Break in Module xdrs at ./paper/tdpr_demo.sv line 8
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/rm1 

*/
