set str "[rsv_print_license]
`timescale 1ns/1ps

import ovm_pkg::*;
import mti_fli::*;
import rsv_solyr_pkg::*;
import usr_solyr_pkg::*;

`include \"ovm_macros.svh\"
`include \"rsv_defines.svh\"

module $rr_
(
[rsv_print_portmap $ri_ io ,\n]
);

//-------------------------------------------------------------------
// Declarations
//-------------------------------------------------------------------

	`define NUM_RM $l_ // Number of reconfigurable modules in this region
	`define NUM_FR $sz_ // Number of configuration frames of this region

	typedef virtual interface $ri_ ${ri_}_type;
	typedef virtual interface portal_if#(`NUM_RM) portal_if_type;
	typedef virtual interface state_if#(`NUM_FR) state_if_type;

	`define rsv_init_portal(rmid_, pif, nm_, sgnt_) begin    \\
		pif.module_names\[rmid_\] = nm_;                       \\
		pif.module_sgnts\[rmid_\] = sgnt_;                     \\
	end

	`define rsv_select_module_out(sig_)                 \\
	always @(*) begin case (pif.active_module_id)       \\
[rsv_print_region $rr_ slrmo \n]
		default: begin rm_rif.sig_ = rm0_rif.sig_; end  \\
	endcase end
	
	`define rsv_select_module_in(sig_)                  \\
	always @(*) begin case (pif.active_module_id)       \\
[rsv_print_region $rr_ slrmi \n]
		default: begin rm0_rif.sig_ = rm_rif.sig_; end  \\
	endcase end
	
	`define rsv_select_phase_out(sig_)                  \\
	always @(*) begin case (pif.reconf_phase)           \\
		8'h0: begin sta_rif.sig_ = rm_rif.sig_; end     \\
		8'h1: begin if (eif.sei_en) sta_rif.sig_ = sei_rif.sig_; if (eif.dei_en) dei_rif.sig_ = rm_rif.sig_; end \\
		default: begin sta_rif.sig_ = rm_rif.sig_; end  \\
	endcase end
	
	`define rsv_select_phase_in(sig_)                   \\
	always @(*) begin case (pif.reconf_phase)           \\
		8'h0: begin rm_rif.sig_ = sta_rif.sig_; end     \\
		8'h1: begin if (eif.dei_en) rm_rif.sig_ = dei_rif.sig_; if (eif.dei_en) sei_rif.sig_ = sta_rif.sig_; end \\
		default: begin rm_rif.sig_ = sta_rif.sig_; end  \\
	endcase end
	
//-------------------------------------------------------------------
// Selecting the active reconfigurable module
//-------------------------------------------------------------------

	// Portal interface:
	//
	// The portal selects the current active module and the reconfiguration 
	// phase. The source of portal selection is from the class-based environment

	portal_if #(`NUM_RM) pif();
	
	initial begin
[rsv_print_region $rr_ pif \n]

	end
	
	// Selecting IO signals of the dynamic side:
	//
	// The IO signals of parallel connected reconfigurable modules 
	// (dynamic side) are interleaved and only one set of IO signals 
	// is active at a time. The selection mimics the swapping of modules 
	// and is controlled by the portal interface, which is in turn 
	// driven by the class-based environment. 

[rsv_print_region $rr_ rif \n]
	$ri_    rm_rif();  // current active module

[rsv_print_portmap $ri_ slrm \n]

	// Connecting IO signals of the static side:
	//
	// The IO signals of the static part of the user logic (static side)
	// are connected to the reconfigurable modules during normal opertion, 
	// or to the error sources during partial reconfiguration. 

	$ri_    sta_rif();

[rsv_print_portmap $ri_ assg \n]

//-------------------------------------------------------------------
// Selecting the reconfiguration phase
//-------------------------------------------------------------------

	// Error interface: 
	//
	// During reconfiguration, errors are injected to both static region (SEI) 
	// and the active reconfigurable module in the dynamic region (DEI). The 
	// selection of reconfiguration phase is controlled by the portal interface 
	// whereas the error interface enables/disables the error sources. Both 
	// interfaces are driven by the class-based environment

	error_if eif();

	always @(*) begin
		eif.active_module_id   = pif.active_module_id;
		eif.reconf_phase       = pif.reconf_phase;
	end
	
	// Selecting the error sources:
	//
	// Error injection mimics the un-defined output to both static & dynamic 
	// sides DURING reconfiguration. Errors injected towoards the static 
	// side stress tests the isolation mechanism of user logic; errors
	// injected to the dynamic side mimics the undifined state of 
	// reconfigurable modules, and assists the testing of the initialization 
	// mechanism of the user logic. The source of the error comes from the 
	// class-based environment
	
	$ri_    sei_rif(); // error source to the static side
	$ri_    dei_rif(); // error source to the dynamic side
	
[rsv_print_portmap $ri_ slei \n]

//-------------------------------------------------------------------
// State saving/restoring
//-------------------------------------------------------------------

	// State interface:
	//
	// On capture or restore, the state interface is synchronized
	// with the HDL signals (i.e., GCAPTURE: HDL->configuration 
	// memory, GRESTORE: configuration memory -> HDL).
	// 
	// The configuration data is stored in the state interface. 
	// and is maintained by the state_spy artifacts of the class-based part. 
	
	state_if #(`NUM_FR)  rm_sif();
	
	chandle interp;
	initial begin
		interp = mti_Interp();
		
[rsv_print_region $rr_ rstate \n $id_]

	end
	
	always @(*) begin
		rm_sif.active_module_id   = pif.active_module_id;
		rm_sif.reconf_phase       = pif.reconf_phase;
		rm_sif.signature          = pif.module_sgnts\[pif.active_module_id\];
	end

//-------------------------------------------------------------------
// Functional Coverage for module swapping
//-------------------------------------------------------------------

`ifdef MTI_QUESTA

	covergroup cvg_${rr_}_drp @pif.active_module_id;
		active_module: coverpoint pif.active_module_id {
			bins cur\[\] = {\[0:`NUM_RM-1\]};
			illegal_bins other = default;
		}
		module_transition: coverpoint pif.active_module_id {
			bins cfg\[\] = (\[0:`NUM_RM-1\] => \[0:`NUM_RM-1\]);
			ignore_bins cfg_no_change = [rsv_print_region $rr_ ignorebin ,];
			illegal_bins other = default sequence;
		}
	endgroup
	
	cvg_${rr_}_drp cvg_0 = new;

`endif

//-------------------------------------------------------------------
// Configuring the Simulation-only Layer
//-------------------------------------------------------------------

	// Pass the interface(s) to the virtual interface(s) in solyr,
	// & parameterize the testbench classes with the user-defined interface(s)

	initial begin

		// Mentor Graphics reconmmend to wrap the interface into a class and use
		// set_config_object to pass interface of module-based DUT to the
		// virtual interface of the class-based verification environment.
		// Here, the convenient macro set_config_interface help you to do that

		`set_config_interface(rsv_if_wrapper #(portal_if_type), \"*.rr${id_}.pc\", \"pif_tag\", pif)
		`set_config_interface(rsv_if_wrapper #(state_if_type), \"*.rr${id_}.ss\", \"spy_tag\", rm_sif)
		`set_config_interface(rsv_if_wrapper #(error_if_type), \"*.rr${id_}.ei\", \"ei_tag\", eif)
		`set_config_interface(rsv_if_wrapper #(${ri_}_type), \"*.rr${id_}.ei\", \"sei_tag\", sei_rif)
		`set_config_interface(rsv_if_wrapper #(${ri_}_type), \"*.rr${id_}.ei\", \"dei_tag\", dei_rif)
		`set_config_interface(rsv_if_wrapper #(${ri_}_type), \"*.rr${id_}.rec\", \"rec_tag\", sta_rif)

		// Set number of reconfigurable modules to the desired value
		// Set number of words in the spy memory to the desired value
		// Set number of signals in the state spy to the desired value

		set_config_int(\"*.rr${id_}.pc\", \"num_rm\", `NUM_RM);
		set_config_int(\"*.rr${id_}.ss\", \"num_fr\", `NUM_FR);

		// Set instantiation hierarchy path in artifacts 
		
		set_config_string(\"*.rr${id_}.pc\", \"rr_inst\", \$psprintf(\"%m\"));
		set_config_string(\"*.rr${id_}.ei\", \"rr_inst\", \$psprintf(\"%m\"));
		set_config_string(\"*.rr${id_}.ss\", \"rr_inst\", \$psprintf(\"%m\"));
		set_config_string(\"*.rr${id_}.rec\", \"rr_inst\", \$psprintf(\"%m\"));
		
		// Enable transaction recording by default
		
		set_config_int(\"*.rr${id_}.rec\", \"is_record_trans\", 1);
		
		// Set your own classes here using the factory mechanism of OVM.
		// You can change the components within the simulation-only layer without editing
		// the source code of the library, for example, if you define your own version of region recorder
		// and error injector, you can replace the default code with your own code, for example:
		//
		//     rsv_error_injector_base::type_id::set_inst_override(my_error_injector::get_type(), \"*.rr?.ei\");
		//     rsv_region_recorder_base::type_id::set_inst_override(my_region_recorder::get_type(), \"*.rr?.rec\");
		//
		// As a quick start, you can use the generated default code, which is
		// parameterized with the user-defined interface, and consumes the incomming
		// transactions without processing them, for example:
		//
		//     rsv_error_injector_base::type_id::set_inst_override(rsv_error_injector#(${ri_}_type)::get_type(), \"*.rr?.ei\");
		//     rsv_region_recorder_base::type_id::set_inst_override(my_region_recorder#(${ri_}_type)::get_type(), \"*.rr?.rec\");
		//
		// For more information about factory, see the OVM User Guide

		rsv_portal_controller_base::type_id::set_inst_override(rsv_portal_controller#(portal_if_type)::get_type(), \"*.rr${id_}.pc\");
		rsv_state_spy_base::type_id::set_inst_override(rsv_state_spy#(state_if_type)::get_type(), \"*.rr${id_}.ss\");
		rsv_error_injector_base::type_id::set_inst_override(${ei_}::get_type(), \"*.rr${id_}.ei\");
		rsv_region_recorder_base::type_id::set_inst_override(${rec_}::get_type(), \"*.rr${id_}.rec\");

	end

//-------------------------------------------------------------------
// Instantiating reconfigurable modules
//-------------------------------------------------------------------

[rsv_print_region $rr_ module \n\n]

endmodule


"
