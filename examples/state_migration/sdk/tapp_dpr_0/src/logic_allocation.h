/****************************************************************************
*
* Porject:     State Migration Application
* Filename:    logic_allocation.h
* Description: Logic allocation for registers/memory cells
* Date:        7 Mar. 2012
*
*****************************************************************************/

#ifndef LOGIC_ALLOCATION_H_
#define LOGIC_ALLOCATION_H_

#ifdef __cplusplus
extern "C" {
#endif

#ifdef BOARD_ML507
/*********************************************************************
 * math_core::adder::statistic[15:0]
 * 
 *    0x0001859e:
 *        283 statistic[1];  347 statistic[5];  411 statistic[9];  475 statistic[13]
 *    0x0001859f:
 *        258 statistic[0];  295 statistic[2];  317 statistic[3];  322 statistic[4];
 *        359 statistic[6];  381 statistic[7];  386 statistic[8];  423 statistic[10];
 *        445 statistic[11]; 450 statistic[12]; 487 statistic[14]; 509 statistic[15];
 *    
 ********************************************************************/
static CfgOneBit_t mca_statistic_frame_0[4] = {
	{1,283}, {5,347}, {9,411},{13,475}
};
static CfgOneBit_t mca_statistic_frame_1[12] = {
	{0,258}, {2,295}, {3,317}, {4,322}, 
	{6,359}, {7,381}, {8,386}, {10,423},
	{11,445},{12,450},{14,487},{15,509}
};
static CfgOneFrame_t mca_statistic_frame_array[2] = {
	{0x0001859e, 4, mca_statistic_frame_0}, {0x0001859f, 12, mca_statistic_frame_1}
};
CfgStateLl_t mca_statistic_ll = {2, mca_statistic_frame_array};

/*********************************************************************
 * math_core::adder::result[31:0]
 * 
 *    0x0001839f:
 *          3 result[0] ;  28 result[1] ;  40 result[2] ;  62 result[3] ;
 *         67 result[4] ;  92 result[5] ; 104 result[6] ; 126 result[7] ;
 *        131 result[8] ; 156 result[9] ; 168 result[10]; 190 result[11];
 *        195 result[12]; 220 result[13]; 232 result[14]; 254 result[15];
 *        259 result[16]; 284 result[17]; 296 result[18]; 318 result[19];
 *        323 result[20]; 348 result[21]; 360 result[22]; 382 result[23];
 *        387 result[24]; 412 result[25]; 424 result[26]; 446 result[27];
 *        451 result[28]; 476 result[29]; 488 result[30]; 510 result[31];
 *    
 ********************************************************************/
static CfgOneBit_t mca_result_frame_0[32] = {
	{0,3},   {1,28},  {2,40},  {3,62},  
	{4,67},  {5,92},  {6,104}, {7,126},
	{8,131}, {9,156}, {10,168},{11,190},
	{12,195},{13,220},{14,232},{15,254},
	{16,259},{17,284},{18,296},{19,318},
	{20,323},{21,348},{22,360},{23,382},
	{24,387},{25,412},{26,424},{27,446},
	{28,451},{29,476},{30,488},{31,510}
};
static CfgOneFrame_t mca_result_frame_array[1] = {
	{0x0001839f, 32, mca_result_frame_0}
};
CfgStateLl_t mca_result_ll = {1, mca_result_frame_array};

/*********************************************************************
 * math_core::maximum::statistic[15:0]
 * 
 *    0x0001859e:
 *        283 statistic[1] ; 347 statistic[5] ; 411 statistic[9] ; 475 statistic[13]; 
 *    0x0001859f:
 *        258 statistic[0] ; 295 statistic[2] ; 317 statistic[3] ; 322 statistic[4] ; 
 *        359 statistic[6] ; 381 statistic[7] ; 386 statistic[8] ; 423 statistic[10]; 
 *        445 statistic[11]; 450 statistic[12]; 487 statistic[14]; 509 statistic[15]; 
 *
 ********************************************************************/
static CfgOneBit_t mcm_statistic_frame_0[4] = {
	{1,283}, {5,347}, {9,411}, {13,475}
};
static CfgOneBit_t mcm_statistic_frame_1[12] = {
	{0,258}, {2,295}, {3,317}, {4,322}, 
	{6,359}, {7,381}, {8,386}, {10,423},
	{11,445},{12,450},{14,487},{15,509}
};
static CfgOneFrame_t mcm_statistic_frame_array[2] = {
	{0x0001859e, 4,  mcm_statistic_frame_0},
	{0x0001859f, 12, mcm_statistic_frame_1}
};
CfgStateLl_t mcm_statistic_ll = {2, mcm_statistic_frame_array};

/*********************************************************************
 * math_core::maximum::result[31:0]
 *    
 *    0x0001839f:
 *          3 result[0] ;  28 result[1] ;  40 result[2] ;  62 result[3] ; 
 *    0x0001831e:
 *        155 result[13]; 
 *    0x0001831f:
 *         67 result[4] ;  92 result[5] ; 104 result[6] ; 126 result[7] ; 
 *        130 result[12]; 167 result[14]; 189 result[15]; 
 *    0x0001841e:
 *        219 result[21]; 283 result[25]; 
 *    0x0001841f:
 *        195 result[16]; 220 result[17]; 232 result[18]; 254 result[19]; 
 *        194 result[20]; 231 result[22]; 253 result[23]; 258 result[24]; 
 *        295 result[26]; 317 result[27]; 
 *    0x0001849f:
 *        387 result[28]; 412 result[29]; 424 result[30]; 446 result[31]; 
 *    0x0001851e:
 *        219 result[9] ; 
 *    0x0001851f:
 *        194 result[8] ; 231 result[10]; 253 result[11]; 
 *
 ********************************************************************/
static CfgOneBit_t mcm_result_frame_0[4]   = {{0,3},    {1,28},   {2,40},   {3,62}};
static CfgOneBit_t mcm_result_frame_1[1]   = {{13,155}};
static CfgOneBit_t mcm_result_frame_2[7]   = {
	{4,67},   {5,92},   {6,104},  {7,126}, 
	{12,130}, {14,167}, {15,189}
};
static CfgOneBit_t mcm_result_frame_3[2]   = {{21,219}, {25,283}};
static CfgOneBit_t mcm_result_frame_4[10]  = {
	{16,195}, {17,220}, {18,232}, {19,254}, 
	{20,194}, {22,231}, {23,253}, {24,258}, 
	{26,295}, {27,317}
};
static CfgOneBit_t mcm_result_frame_5[4]   = {{28,387}, {29,412}, {30,424}, {31,446}};
static CfgOneBit_t mcm_result_frame_6[1]   = {{9, 219}};
static CfgOneBit_t mcm_result_frame_7[3]   = {{8, 194}, {10,231}, {11,253}};
static CfgOneFrame_t mcm_result_frame_array[8] = {
	{0x0001839f, 4,  mcm_result_frame_0}, {0x0001831e, 1,  mcm_result_frame_1}, 
	{0x0001831f, 7,  mcm_result_frame_2}, {0x0001841e, 2,  mcm_result_frame_3}, 
	{0x0001841f, 10, mcm_result_frame_4}, {0x0001849f, 4,  mcm_result_frame_5}, 
	{0x0001851e, 1,  mcm_result_frame_6}, {0x0001851f, 3,  mcm_result_frame_7}, 
};
CfgStateLl_t mcm_result_ll = {8, mcm_result_frame_array};

#else /* ReSim */

/*********************************************************************
 * adder.sll:
 *     0x00000001 32 32 statistic
 *     0x00000002 48 32 result
 ********************************************************************/
 
/* math_core::adder::statistic[31:0] */
static CfgOneBit_t mca_statistic_frame_0[32] = {
	{0,32},  {1,33},  {2,34},  {3,35},  {4,36},  {5,37},  {6,38},  {7,39},
	{8,40},  {9,41},  {10,42}, {11,43}, {12,44}, {13,45}, {14,46}, {15,47},
	{16,48}, {17,49}, {18,50}, {19,51}, {20,52}, {21,53}, {22,54}, {23,55},
	{24,56}, {25,57}, {26,58}, {27,59}, {28,60}, {29,61}, {30,62}, {31,63}
};
static CfgOneFrame_t mca_statistic_frame_array[1] = {
	{0x00000001, 32, mca_statistic_frame_0}
};
CfgStateLl_t mca_statistic_ll = {1, mca_statistic_frame_array};

/* math_core::adder::result[31:0] */
static CfgOneBit_t mca_result_frame_0[32] = {
	{0,48},  {1,49},  {2,50},  {3,51},  {4,52},  {5,53},  {6,54},  {7,55},
	{8,56},  {9,57},  {10,58}, {11,59}, {12,60}, {13,61}, {14,62}, {15,63},
	{16,64}, {17,65}, {18,66}, {19,67}, {20,68}, {21,69}, {22,70}, {23,71},
	{24,72}, {25,73}, {26,74}, {27,75}, {28,76}, {29,77}, {30,78}, {31,79}
};
static CfgOneFrame_t mca_result_frame_array[1] = {
	{0x00000002, 32, mca_result_frame_0}
};
CfgStateLl_t mca_result_ll = {1, mca_result_frame_array};

/*********************************************************************\
 * maximum.sll:
 *     0x00010002 36 32 statistic
 *     0x00010000 36 32 result
 ********************************************************************/
 
/* math_core::maximum::statistic[31:0] */
static CfgOneBit_t mcm_statistic_frame_0[32] = {
	{0,36},  {1,37},  {2,38},  {3,39},  {4,40},  {5,41},  {6,42},  {7,43},
	{8,44},  {9,45},  {10,46}, {11,47}, {12,48}, {13,49}, {14,50}, {15,51},
	{16,52}, {17,53}, {18,54}, {19,55}, {20,56}, {21,57}, {22,58}, {23,59},
	{24,60}, {25,61}, {26,62}, {27,63}, {28,64}, {29,65}, {30,66}, {31,67}
};
static CfgOneFrame_t mcm_statistic_frame_array[1] = {
	{0x00010002, 32, mcm_statistic_frame_0}
};
CfgStateLl_t mcm_statistic_ll = {1, mcm_statistic_frame_array};

/* math_core::maximum::result[31:0] */
static CfgOneBit_t mcm_result_frame_0[32] = {
	{0,36},  {1,37},  {2,38},  {3,39},  {4,40},  {5,41},  {6,42},  {7,43},
	{8,44},  {9,45},  {10,46}, {11,47}, {12,48}, {13,49}, {14,50}, {15,51},
	{16,52}, {17,53}, {18,54}, {19,55}, {20,56}, {21,57}, {22,58}, {23,59},
	{24,60}, {25,61}, {26,62}, {27,63}, {28,64}, {29,65}, {30,66}, {31,67}
};
static CfgOneFrame_t mcm_result_frame_array[1] = {
	{0x00010000, 32, mcm_result_frame_0}
};
CfgStateLl_t mcm_result_ll = {1, mcm_result_frame_array};

#endif


#ifdef __cplusplus
}
#endif

#endif 
