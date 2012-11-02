
source settings.do; 

# Importing the ReSim library

namespace import ReSim::*

# Create a portmap and add ports to it. The portmap can have an optional clk
# which is always 1 bit input to the portmap

rsv_create_portmap "my_if" "clk"

rsv_add_port "my_if" "rstn"       in
rsv_add_port "my_if" "rc_reqn"    in
rsv_add_port "my_if" "rc_ackn"    out
rsv_add_port "my_if" "p_prdy"     out
rsv_add_port "my_if" "p_crdy"     in
rsv_add_port "my_if" "p_cerr"     in
rsv_add_port "my_if" "p_data"     out 32
rsv_add_port "my_if" "c_prdy"     in
rsv_add_port "my_if" "c_crdy"     out
rsv_add_port "my_if" "c_cerr"     out
rsv_add_port "my_if" "c_data"     in  32

# Create reconfigurable regions and add modules to it. The region can have
# an optional error injector. In this example, the region use "my_if" portmap, 
# contains 4 configuration frames, and uses an the "my_ei_edited" error injector
#
# For modules that use non-default parameters, pass the real parameters 
# as the last argument of "rsv_add_module" in the format of a string.
# In this example, we overwrite the C_CNT_BW parameter with 48 and 24 for both 
# modules, and we overwirte the C_RETRY_DELAY parameter with 24 for the 
# "reverse" module. ReSim only support positional association for passing 
# module parameters. 

rsv_create_region "my_region" "my_if" 4 "" "my_ei_edited"

rsv_add_module "my_region" "maximum" "#(48)"
rsv_add_module "my_region" "reverse" "#(24,24)"

# Create the simulation-only layer and add reconfigurable regions to it. The 
# simulation-only layer can have an optional scoreboard. In this example, 
# the solyr use a scoreboard ("my_scb"). 
# Then, we generate the source code of all simulation artifacts by calling
# "rsv_gen_solyr"

rsv_create_solyr "my_solyr" VIRTEX4 "my_scb"
rsv_add_region   "my_solyr" "my_region"
rsv_gen_solyr    "my_solyr"

# Optional: The generated SBT are in binary format (./artifacts/sbt/xxxx.sbt)
# and can not be used by simulation directly. The following steps convert the
# binary SBT into a "memory format" that are ready to be loaded into ModelSim.
# Users can also create in-house tools to perform such converstion. 
# 
# The following example merges the sbt into a "zbt" memory, whose granularity
# is 4 byte (word-addressed) and has 1 banks connected in parallel. The endian
# is big endian. The converted SBT files can be found at ./artifacts/sbt/zbt_bank0.txt

rsv_create_memory "zbt" 4 1 be

# Adding SBTs to the memory: E.g., the 1st SBT goes to address 0x100. As the
# granularity is 4 byte (word-addressed), the actual byte-based address is 0x400.

rsv_add_2_memory "zbt" "./artifacts/sbt/my_region_rm0.sbt" 0x100
rsv_add_2_memory "zbt" "./artifacts/sbt/my_region_rm1.sbt" 0x200

# Removing the ReSim library

namespace forget ReSim::*

# Copy backup files to overwite the generated files. The backup files are modified
# based on the corresponding generated files. Such modifications adapt the generated 
# artifacts for design/test specific needs. 

file copy -force "./artifacts.edited/my_ei.edited.txt" "./artifacts/my_ei_edited.svh"

file copy -force "./artifacts.edited/my_region_maximum.edited.txt" "./artifacts/spy/my_region_rm0.sll"
file copy -force "./artifacts.edited/my_region_reverse.edited.txt" "./artifacts/spy/my_region_rm1.sll"

file copy -force "./artifacts.edited/zbt_bank0.rb.txt" "./artifacts/sbt/zbt_bank0.rb.txt"
