
source settings.do; 

ReSim::rsv_create_portmap "my_if" "clk"

ReSim::rsv_add_port "my_if" "rstn"       in
ReSim::rsv_add_port "my_if" "rc_reqn"    in
ReSim::rsv_add_port "my_if" "rc_ackn"    out
ReSim::rsv_add_port "my_if" "p_prdy"     out
ReSim::rsv_add_port "my_if" "p_crdy"     in
ReSim::rsv_add_port "my_if" "p_cerr"     in
ReSim::rsv_add_port "my_if" "p_data"     out 32
ReSim::rsv_add_port "my_if" "c_prdy"     in
ReSim::rsv_add_port "my_if" "c_crdy"     out
ReSim::rsv_add_port "my_if" "c_cerr"     out
ReSim::rsv_add_port "my_if" "c_data"     in  32

ReSim::rsv_create_region "my_region" "my_if" 4 "my_monitor" "my_ei"

ReSim::rsv_add_module "my_region" "maximum" "#(48)"
ReSim::rsv_add_module "my_region" "reverse" "#(24,24)"

ReSim::rsv_create_solyr "my_solyr" VIRTEX4 "my_scb"
ReSim::rsv_add_region   "my_solyr" "my_region"
ReSim::rsv_gen_solyr    "my_solyr"

ReSim::rsv_create_memory "zbt" 4 1 be

ReSim::rsv_add_2_memory "zbt" "./artifacts/sbt/my_region_rm0.sbt" 0x100
ReSim::rsv_add_2_memory "zbt" "./artifacts/sbt/my_region_rm1.sbt" 0x200
