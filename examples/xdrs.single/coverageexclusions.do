onerror {resume}

## Can also use vsim -voptargs=-nofsmresettrans to avoid counting reset-related 
## state transitions in the coverage analysis. In this case, I still prefer to 
## use explict exclusion
## =====================================================================

coverage exclude -du icapi -ftrans state_c \
	{st1->st0} {st2->st0} {st3->st0} {st4->st0} {st5->st0} {st6->st0} {st7->st0}

coverage exclude -du maximum -ftrans state_c \
	{S_Rd1->S_IDLE} {S_Rd2->S_IDLE} {S_ReTry->S_IDLE}

coverage exclude -du reverse -ftrans state_c \
	{S_Rd1->S_IDLE} {S_Rd2->S_IDLE} {S_Wr1->S_IDLE} {S_ReTry1->S_IDLE} {S_ReTry2->S_IDLE}

coverage exclude -scope /xdrs/icapi_0/icap_0

## I have add an timeout counter in the maximum/reverse cores respectively
## so now the cores may drive cerr=1, and the following exclusions are not needed anymore
## ====================================================================================
## 
## coverage exclude -src ./xdrs/isolator.v -fecexprrow 47 4
## coverage exclude -src ./xdrs/isolator.v -exprrow 47 5
## coverage exclude -src ./xdrs/isolator.v -exprrow 47 3

## The following FEC rows are because of redundancy in RTL code. As they will never occur
## I excluded them from coverage analysis
## ====================================================================================
coverage exclude -src ./xdrs/cores/maximum.v -fecexprrow 88 3
coverage exclude -src ./xdrs/cores/maximum.v -fecexprrow 89 3
coverage exclude -src ./xdrs/cores/reverse.v -fecexprrow 90 3
coverage exclude -src ./xdrs/cores/reverse.v -fecexprrow 91 3
