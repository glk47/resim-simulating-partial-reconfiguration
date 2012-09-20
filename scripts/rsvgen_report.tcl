set str "==== Name: $vf_ 
==== Time: [clock format [clock seconds] -format  {%H:%M:%S, %B %d, %Y}] 
+-----------------------------------+-------------------------+
;     region_name / module_name     ;  rrid(hex) / rmid(hex)  ;
+-----------------------------------+-------------------------+
[rsv_print_fpga $vf_ rr \n _id]
+-----------------------------------+-------------------------+

rrid: reconfigurable region id
rmid: reconfigurable modue id

"
