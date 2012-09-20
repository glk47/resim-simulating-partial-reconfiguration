
`ifdef TEST_DPR_STREAMING

	initial begin
		#1
		ovm_top.ovm_report_info("XDRS", "Running test: TEST_DPR_STREAMING");
		ovm_top.set_report_verbosity_level_hier(OVM_MEDIUM);
		
		#80_000 $finish();
	end
	
	/* producer thread: producer -> core */
	initial begin
		#10_000
		
		fork begin
			pc_0.produce_data(32'h1);
			repeat(64) pc_0.produce_data(32'h0);
		end join_none
		
		#10_000;
		
		fork begin
			pc_0.produce_data(32'h1);
			repeat(64) pc_0.produce_data(32'h0);
		end join_none
		
		#20_000;
		
		fork begin
			pc_0.produce_data(32'h1);
			repeat(64) pc_0.produce_data(32'h0);
		end join_none
		
		#20_000;
		ovm_top.set_report_verbosity_level_hier(OVM_MEDIUM);
		fork begin
			repeat(128) pc_0.produce_data($urandom());
		end join_none
		
	end

	/* consumer thread: core -> consumer */
	initial begin
		logic [31:0] data;

		#5_000

		forever begin
			pc_0.consume_data_nodelay(data);
		end

	end
	
	/* reconfiguration manager thread: reconfigure modules */
	initial begin
		#18_000
		
		fork begin
			mgr_0.reconfigure_module(8'b0010_0001, `RM_2_1_ADDR, (`RM_2_1_SIZE+`SBT_HEADER_SIZE));
		end join_none
		
		#22_500

		fork begin
			mgr_0.reconfigure_module(8'b0010_0000, `RM_2_0_ADDR, (`RM_2_0_SIZE+`SBT_HEADER_SIZE));
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
# OVM_INFO @ 1.000ns: reporter [XDRS] Running test: TEST_DPR_STREAMING
# OVM_INFO @ 5.000ns: solyr.rr2.mon [ReSim] [DURING_PH @ 5.000ns] USR_OP::ErrInjection, Starting X Injection
# OVM_INFO @ 5.000ns: solyr.rr1.mon [ReSim] [DURING_PH @ 5.000ns] USR_OP::ErrInjection, Starting X Injection
# OVM_INFO @ 5.000ns: solyr.rr0.mon [ReSim] [DURING_PH @ 5.000ns] USR_OP::ErrInjection, Starting X Injection
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/gen_rr/gen_0/math_0/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_0/gen_rr/gen_0/math_0/rm1 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_1/gen_rr/gen_1/math_1/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_1/gen_rr/gen_1/math_1/rm1 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0 
# [SKT] Registering Simulator Kernel Thread (SKT): /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1 
# OVM_INFO @ 18005.000ns: reporter [MANAGER] Reconfigure module: rrid:2 rmid:1
# OVM_INFO @ 26190.000ns: solyr.rr2.mon [ReSim] [DURING_PH @ 26105.000ns] SBT_OP::WCFG, rrid= 0x02, rmid= 0x01, module= lpfilter_2_rr.lpfilter
# [SKT] Reconfigurable Module swapped in: /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1 
# [SKT] Reconfigurable Module swapped out: /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0 
# OVM_INFO @ 28635.000ns: reporter [MANAGER] Reconfiguration DONE
# OVM_INFO @ 40505.000ns: reporter [MANAGER] Reconfigure module: rrid:2 rmid:0
# OVM_INFO @ 41650.000ns: solyr.rr2.mon [ReSim] [DURING_PH @ 41565.000ns] SBT_OP::WCFG, rrid= 0x02, rmid= 0x00, module= lpfilter_2_rr.lpfilter
# [SKT] Reconfigurable Module swapped out: /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1 
# [SKT] Reconfigurable Module swapped in: /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0 
# OVM_INFO @ 44095.000ns: reporter [MANAGER] Reconfiguration DONE
# Break in Module xdrs at ./xtests/tdpr_streaming.sv line 9
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/gen_rr/gen_0/math_0/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_0/gen_rr/gen_0/math_0/rm1 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_1/gen_rr/gen_1/math_1/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_1/gen_rr/gen_1/math_1/rm1 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm0 
# [SKT] Un-registering Simulator Kernel Thread (SKT): /xdrs/region_2/gen_rr/gen_2/lpfilter_2/rm1 

*/
