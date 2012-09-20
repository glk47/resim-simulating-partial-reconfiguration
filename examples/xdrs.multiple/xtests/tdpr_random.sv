
`ifdef TEST_DPR_RANDOM

	initial begin
		#1
		ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_RANDOM");
		ovm_top.set_report_verbosity_level_hier(OVM_MEDIUM);
		
		#100_000 $finish();
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
			pc_0.consume_data_nodelay(data);
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
		#20_000
		
		fork begin
			mgr_0.reconfigure_module(8'b0010_0001, `RM_2_1_ADDR, (`RM_2_1_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
		#20_000

		fork begin
			mgr_0.reconfigure_module(8'b0010_0000, `RM_2_0_ADDR, (`RM_2_0_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
		#20_000
		
		fork begin
			mgr_0.reconfigure_module(8'b0000_0001, `RM_0_1_ADDR, (`RM_0_1_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
		#10_000
		
		fork begin
			mgr_0.reconfigure_module(8'b0001_0001, `RM_1_1_ADDR, (`RM_1_1_SIZE+`SBT_HEADER_SIZE));
		end join_none

		#10_000

		fork begin
			mgr_0.reconfigure_module(8'b0001_0000, `RM_1_0_ADDR, (`RM_1_0_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
		#10_000

		fork begin
			mgr_0.reconfigure_module(8'b0000_0000, `RM_0_0_ADDR, (`RM_0_0_SIZE+`SBT_HEADER_SIZE));
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
# OVM_WARNING D:/My_Designs/UNSW_DRS/ReSim/src/rsv_monitor.svh(98) @ 0.000ns: solyr.rr2.mon [ReSim] Using the default monitor
# OVM_WARNING D:/My_Designs/UNSW_DRS/ReSim/src/rsv_monitor.svh(102) @ 0.000ns: solyr.rr2.mon [ReSim] Using the default monitor
# OVM_WARNING D:/My_Designs/UNSW_DRS/ReSim/src/rsv_monitor.svh(98) @ 0.000ns: solyr.rr1.mon [ReSim] Using the default monitor
# OVM_WARNING D:/My_Designs/UNSW_DRS/ReSim/src/rsv_monitor.svh(102) @ 0.000ns: solyr.rr1.mon [ReSim] Using the default monitor
# OVM_WARNING D:/My_Designs/UNSW_DRS/ReSim/src/rsv_monitor.svh(98) @ 0.000ns: solyr.rr0.mon [ReSim] Using the default monitor
# OVM_WARNING D:/My_Designs/UNSW_DRS/ReSim/src/rsv_monitor.svh(102) @ 0.000ns: solyr.rr0.mon [ReSim] Using the default monitor
# OVM_INFO @ 1.000ns: reporter [XDRS] Running test: TEST_DPR_RANDOM
# OVM_INFO @ 5.000ns: solyr.rr2.mon [ReSim] [DURING_PH @ 5.000ns] USR_OP::ErrInjection, Starting X Injection
# OVM_INFO @ 5.000ns: solyr.rr1.mon [ReSim] [DURING_PH @ 5.000ns] USR_OP::ErrInjection, Starting X Injection
# OVM_INFO @ 5.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 5.000ns] USR_OP::ErrInjection, Starting X Injection
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/gen_rr/gen_0/math_0/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/gen_rr/gen_0/math_0/rm1 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_1/gen_rr/gen_1/math_1/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_1/gen_rr/gen_1/math_1/rm1 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1 
# OVM_INFO @ 20005.000ns: reporter [MANAGER] Reconfigure module: rrid:2 rmid:1
# OVM_INFO @ 28050.000ns: solyr.rr2.mon [ReSim] [DURING_PH @ 27965.000ns] SBT_OP::WCFG, rrid= 0x02, rmid= 0x01, module= lpfilter_2_rr.lpfilter
# [SKT] Reconfigurable Module swapped in: /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1 
# [SKT] Reconfigurable Module swapped out: /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0 
# OVM_INFO @ 30995.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 40005.000ns: reporter [MANAGER] Reconfigure module: rrid:2 rmid:0
# OVM_INFO @ 41210.000ns: solyr.rr2.mon [ReSim] [DURING_PH @ 41125.000ns] SBT_OP::WCFG, rrid= 0x02, rmid= 0x00, module= lpfilter_2_rr.lpfilter
# [SKT] Reconfigurable Module swapped out: /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1 
# [SKT] Reconfigurable Module swapped in: /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0 
# OVM_INFO @ 44295.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 60005.000ns: reporter [MANAGER] Reconfigure module: rrid:0 rmid:1
# OVM_INFO @ 61150.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 61065.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x01, module= math_0_rr.reverse
# [SKT] Reconfigurable Module swapped in: /xdrs/region_0/gen_rr/gen_0/math_0/rm1 
# [SKT] Reconfigurable Module swapped out: /xdrs/region_0/gen_rr/gen_0/math_0/rm0 
# OVM_INFO @ 63375.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 70005.000ns: reporter [MANAGER] Reconfigure module: rrid:1 rmid:1
# OVM_INFO @ 71330.000ns: solyr.rr1.mon [ReSim] [DURING_PH @ 71245.000ns] SBT_OP::WCFG, rrid= 0x01, rmid= 0x01, module= math_1_rr.maximum
# [SKT] Reconfigurable Module swapped in: /xdrs/region_1/gen_rr/gen_1/math_1/rm1 
# [SKT] Reconfigurable Module swapped out: /xdrs/region_1/gen_rr/gen_1/math_1/rm0 
# OVM_INFO @ 73735.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 80005.000ns: reporter [MANAGER] Reconfigure module: rrid:1 rmid:0
# OVM_INFO @ 81370.000ns: solyr.rr1.mon [ReSim] [DURING_PH @ 81225.000ns] SBT_OP::WCFG, rrid= 0x01, rmid= 0x00, module= math_1_rr.reverse
# [SKT] Reconfigurable Module swapped out: /xdrs/region_1/gen_rr/gen_1/math_1/rm1 
# [SKT] Reconfigurable Module swapped in: /xdrs/region_1/gen_rr/gen_1/math_1/rm0 
# OVM_INFO @ 83415.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 90005.000ns: reporter [MANAGER] Reconfigure module: rrid:0 rmid:0
# OVM_INFO @ 90970.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 90885.000ns] SBT_OP::WCFG, rrid= 0x00, rmid= 0x00, module= math_0_rr.maximum
# [SKT] Reconfigurable Module swapped out: /xdrs/region_0/gen_rr/gen_0/math_0/rm1 
# [SKT] Reconfigurable Module swapped in: /xdrs/region_0/gen_rr/gen_0/math_0/rm0 
# OVM_INFO @ 93195.000ns: reporter [MANAGER] Reconfiguration DONE
# Break in Module xdrs at ./xtests/tdpr_random.sv line 9
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/gen_rr/gen_0/math_0/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/gen_rr/gen_0/math_0/rm1 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_1/gen_rr/gen_1/math_1/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_1/gen_rr/gen_1/math_1/rm1 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1 

*/
