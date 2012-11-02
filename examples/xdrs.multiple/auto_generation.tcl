
source settings.do;

# Generate the simulation-only layer ... 

namespace import ReSim::*

rsv_create_portmap "my_if" "clk"
rsv_add_port "my_if" "rstn"           in
rsv_add_port "my_if" "rc_reqn"        in
rsv_add_port "my_if" "rc_ackn"        out
rsv_add_port "my_if" "p_prdy"         out
rsv_add_port "my_if" "p_crdy"         in
rsv_add_port "my_if" "p_cerr"         in
rsv_add_port "my_if" "p_data"         out 32
rsv_add_port "my_if" "c_prdy"         in
rsv_add_port "my_if" "c_crdy"         out
rsv_add_port "my_if" "c_cerr"         out
rsv_add_port "my_if" "c_data"         in  32

# 
# The design has 3 reconfigurable regions: 
# 
# Region rr0 & rr1 are mapped with the same math cores. However in ReSim, regions 
# must have unique names. So rr0 & rr1 are named differently (i.e., "math_0_rr" 
# & "math_1_rr") and are created separately by the "rsv_create_region" API. 
# Region rr2 are mapped with two same lpfilter cores. In ReSim, reconfigurable
# modules can have the same names. 
# 
# Meanwhile rr0 & rr1 share same type of error_injector (i.e., "my_ei"), whereas
# rr2 has its own type of error_injector (i.e., "lpfilter_ei")

rsv_create_region "math_0_rr" "my_if" 4 "" "my_ei"
rsv_add_module "math_0_rr" "maximum" ""
rsv_add_module "math_0_rr" "reverse" ""

rsv_create_region "math_1_rr" "my_if" 4 "" "my_ei"
rsv_add_module "math_1_rr" "reverse" ""
rsv_add_module "math_1_rr" "maximum" ""

rsv_create_region "lpfilter_2_rr" "my_if" 6 "" "lpfilter_ei"
rsv_add_module "lpfilter_2_rr" "lpfilter" "#(0)"
rsv_add_module "lpfilter_2_rr" "lpfilter" "#(1)"

# Create the simulation-only layer with a scoreboard. For multiple
# reconfigurable region designs, the generated scoreboard has pre-defined cross
# coverage such as the cross coverpoint for reconfiguring a region while others 
# are running

rsv_create_solyr "my_solyr" VIRTEX4 "my_scb"
rsv_add_region "my_solyr" "math_0_rr"
rsv_add_region "my_solyr" "math_1_rr"
rsv_add_region "my_solyr" "lpfilter_2_rr"
rsv_gen_solyr "my_solyr"

rsv_create_memory "zbt" 4 1 be

rsv_add_2_memory "zbt" "./artifacts/sbt/math_0_rr_rm0.sbt" 0x100
rsv_add_2_memory "zbt" "./artifacts/sbt/math_0_rr_rm1.sbt" 0x200

rsv_add_2_memory "zbt" "./artifacts/sbt/math_1_rr_rm0.sbt" 0xc00
rsv_add_2_memory "zbt" "./artifacts/sbt/math_1_rr_rm1.sbt" 0xd00

rsv_add_2_memory "zbt" "./artifacts/sbt/lpfilter_2_rr_rm0.sbt" 0xe00
rsv_add_2_memory "zbt" "./artifacts/sbt/lpfilter_2_rr_rm1.sbt" 0xf00

namespace forget ReSim::*

# Copy backup files to overwite the generated files. The lpfilter_2_rr region 
# uses a customized error_injector whereas the math_0_rr & math_1_rr use the 
# default one. The script also copies a pre-defined memory file containing 
# SBT sequences that are used by the testbench

file copy -force "./artifacts.edited/lpfilter_ei.edited.txt" "./artifacts/lpfilter_ei.svh"
file copy -force "./artifacts.edited/zbt_bank0.rb.txt" "./artifacts/sbt/zbt_bank0.rb.txt"
