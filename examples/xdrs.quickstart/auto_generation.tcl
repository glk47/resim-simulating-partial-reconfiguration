
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
# an optional error injector. As a quick start, we use a default error 
# injector ("my_ei"). 
#
# For modules that use non-default parameters, pass the real parameters 
# as the last argument of "rsv_add_module" in the format of a string.
# As a quick start, we use the default parameters so just pass a null string
# to the "rsv_add_module" API. 

rsv_create_region "my_region" "my_if" 4 "" "my_ei"

rsv_add_module "my_region" "maximum" ""
rsv_add_module "my_region" "reverse" ""

# Create the simulation-only layer and add reconfigurable regions to it. The 
# simulation-only layer can have an optional scoreboard. As a quick start,
# we use the default scoreboard. 
# Then, we generate the source code of all simulation artifacts by calling
# "rsv_gen_solyr"

rsv_create_solyr "my_solyr" VIRTEX4 ""
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
