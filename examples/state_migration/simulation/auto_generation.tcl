
source settings.do; 

# Importing the ReSim library

namespace import ReSim::*

# Create a portmap and add ports to it. The portmap can have an optional clk
# which is always 1 bit input to the portmap

rsv_create_portmap "math_if" "clk"

rsv_add_port "math_if" "rst"        in
rsv_add_port "math_if" "ain"        in  32
rsv_add_port "math_if" "bin"        in  32
rsv_add_port "math_if" "result"     out 32
rsv_add_port "math_if" "statistic"  out 32

# Create reconfigurable regions and add modules to it. The region can have
# an optional error injector. In this example, the region use "math_if" portmap, 
# contains 4 configuration frames, and uses an error injector ("math_ei")

rsv_create_region "math_core" "math_if" 4 "" "math_ei"

rsv_add_module "math_core" "adder"   ""
rsv_add_module "math_core" "maximum" ""

# Create the virtual FPGA and add reconfigurable regions to it. The 
# simulation-only layer can have an optional scoreboard.In this example, 
# the solyr do not use any scoreboard. 
# Then, we generate the source code of all simulation artifacts.

rsv_create_solyr "my_solyr" VIRTEX5 ""

rsv_add_region "my_solyr" "math_core"
rsv_gen_solyr "my_solyr"

# Optional: convert the sbt to memory format ready to be loaded into ModelSim
# The following example merges the sbt into a "ddr2" memory, whose granularity
# is 2 byte (16bit-addressed) and has 4 banks connected in parallel. The endian
# is big endian

rsv_create_memory "ddr2" 2 4 be

# Adding SBTs to the memory: E.g., the 1st SBT goes to address 0x20000. As the
# granularity is 2 byte (16bit-addressed), the actual byte-based address is 0x40000

rsv_add_2_memory "ddr2" "./artifacts/sbt/math_core_rm0.sbt" 0x20000
rsv_add_2_memory "ddr2" "./artifacts/sbt/math_core_rm1.sbt" 0x28000

# Project-specific code: use in-house script to further convert SBTs to the 
# desired formate to be loaded to the simulation environment

exec perl ./tb/edit_mem.pl ./artifacts/sbt/ddr2_bank0.txt ./artifacts/sbt/ddr2_bank1.txt
exec perl ./tb/edit_mem.pl ./artifacts/sbt/ddr2_bank2.txt ./artifacts/sbt/ddr2_bank3.txt

# Removing the ReSim library

namespace forget ReSim::*

# Copy backup to the generated files

file copy -force "./artifacts.edited/math_ei.edited.txt" "./artifacts/math_ei.svh"
file copy -force "./artifacts.edited/math_core_adder.edited.txt" "./artifacts/spy/math_core_rm0.sll"
file copy -force "./artifacts.edited/math_core_maximum.edited.txt" "./artifacts/spy/math_core_rm1.sll"
