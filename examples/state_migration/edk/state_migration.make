##############################################################################
## Filename:          system.make
## Description:
## Date:              Sat Mar 01 18:51:31 2012 (by George)
##############################################################################

SYSTEM_XMP_FILE = system.xmp
SYSTEM_MHS_FILE = system.mhs
SYSTEM_MSS_FILE = system.mss

include state_migration_incl.make

############################################################
# PHONY
############################################################
.PHONY: netlist
.PHONY: sdk
.PHONY: sim
.PHONY: clean

############################################################
# TARGETS
############################################################

netlist:
	@echo "************************************************"
	@echo "Running platgen ..."
	@echo "************************************************"
	platgen -p xc5vfx70tff1136-2 -lang verilog -msg __xps/ise/xmsgprops.lst $(SYSTEM_MHS_FILE)
	rm -f platgen.opt platgen.log clock_generator_0.log;
	@echo "************************************************"
	@echo "Running synthesis..."
	@echo "************************************************"
	bash -c "cd synthesis; ./synthesis.sh"
	
	@echo "*********************************************"
	@echo "Copying top-level files: system.ngc/ucf ..."
	@echo "*********************************************"
	
	cp ./implementation/system.ngc ./netlist/system.ngc
	cp ./implementation/system.bmm ./netlist/system.bmm
	cp ./data/system.ucf ./netlist/system.ucf
	
	@echo "*********************************************"
	@echo "Synthesizing math_core::adder ..."
	@echo "*********************************************"
	
	cd ./netlist/math_core/adder; \
	xst -intstyle silent -ifn ./xst_cmd.txt -ofn ./xst_log.txt;           \
	netgen -intstyle silent -sim -ofmt verilog -dir . -w ./math_core.ngc; \
	rm -rf _xmsgs xst;
	
	@echo "*********************************************"
	@echo "Synthesizing math_core::maximum ..."
	@echo "*********************************************"
	
	cd ./netlist/math_core/maximum; \
	xst -intstyle silent -ifn ./xst_cmd.txt -ofn ./xst_log.txt;           \
	netgen -intstyle silent -sim -ofmt verilog -dir . -w ./math_core.ngc; \
	rm -rf _xmsgs xst
	
sdk:
	@echo "************************************************"
	@echo "Exporting to SDK ..."
	@echo "************************************************"
	psf2Edward.exe -inp $(SYSTEM_XMP_FILE) -edwver 1.2 -xml ../sdk/export/hw/system.xml;
	xdsgen.exe -inp $(SYSTEM_XMP_FILE) -report ../sdk/export/hw/system.html  -make_docs_local;
	rm -f psf2Edward.log xdsgen.log;

sim:
	@echo "************************************************"
	@echo "Creating behavioral simulation models ..."
	@echo "************************************************"
	simgen $(SYSTEM_MHS_FILE) \
		-p xc5vfx70tff1136-2 -lang verilog -mixed yes -s mti -m behavioral    \
		-pe ppc440_0 ../sdk/hello_world_0/Debug/hello_world_0.elf \
		-X $(XLIB_HOME) -lp .. -od ..;

clean:
	rm -rf __xps hdl synthesis implementation;
	rm -rf *.log *.opt



