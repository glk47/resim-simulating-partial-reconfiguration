/****************************************************************************
*
* Porject:     State Migration Application
* Filename:    xmath.c
* Description: Software driver for XPS_MATH
* Date:        7 Mar. 2012
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xparameters.h"

#include "xil_io.h"
#include "xmath.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

/****************************************************************************/
/**
* Math_Initialize()
* Math_DoComputation()
*
*****************************************************************************/

int Math_Initialize(MathDriver_t* DrvPtr, u32 DeviceId, u32 BaseAddress) {
	
	DrvPtr->DeviceId = 0;
	DrvPtr->BaseAddress = BaseAddress;
	
	return XST_SUCCESS;
}

u32 Math_DoComputation(MathDriver_t* DrvPtr,u32 first, u32 second) {
	
	Xil_Out32(DrvPtr->BaseAddress,first);
	Xil_Out32(DrvPtr->BaseAddress+4,second);
	
	return Math_GetResult(DrvPtr);
}

/****************************************************************************/
/**
* Math_GetResult()
* Math_GetStatistic()
* Math_SoftReset()
* Math_PauseClock()
* Math_ResumeClock()
*
*****************************************************************************/

u32 Math_GetResult(MathDriver_t* DrvPtr) {
	return Xil_In32(DrvPtr->BaseAddress);
}

u32 Math_GetStatistic(MathDriver_t* DrvPtr) {
	return Xil_In32(DrvPtr->BaseAddress+4);
}

void Math_SoftReset(MathDriver_t* DrvPtr) {
	Xil_Out32(DrvPtr->BaseAddress+0x100,0xA);
}
void Math_PauseClock(MathDriver_t* DrvPtr) {
	Xil_Out32(DrvPtr->BaseAddress+0x200,0x5);
}
void Math_ResumeClock(MathDriver_t* DrvPtr) {
	Xil_Out32(DrvPtr->BaseAddress+0x200,0xA);
}

/****************************************************************************/
/**
* Math_TestComputation(u32 first, u32 second)
* Math_TestReset()
* Math_TestClock()
*
*****************************************************************************/

int Math_TestComputation(MathDriver_t* DrvPtr, u32 first, u32 second) {

	volatile u32 result = Math_DoComputation(DrvPtr, first, second);

	if (Math_GetId(DrvPtr) == MATH_ADDER_ID) {
		Xil_AssertNonvoid( result == (first + second) );
	} else if (Math_GetId(DrvPtr) == MATH_MAXIMUM_ID) {
		Xil_AssertNonvoid( result == ((first > second) ? first : second) );
	} else {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

int Math_TestReset(MathDriver_t* DrvPtr) {

	(void)Math_DoComputation(DrvPtr, 0x3fff, 0x1);
	(void)Math_SoftReset(DrvPtr);

	Xil_AssertNonvoid(Math_GetResult(DrvPtr)== 0);
	Xil_AssertNonvoid(Math_GetCnt(DrvPtr)   == 0);
	Xil_AssertNonvoid((Math_GetId(DrvPtr)==MATH_ADDER_ID) || (Math_GetId(DrvPtr)==MATH_MAXIMUM_ID));

	return XST_SUCCESS;
}

int Math_TestClock(MathDriver_t* DrvPtr) {

	volatile u32 result_old, statistic_old;
	
	result_old    = Math_GetResult(DrvPtr);
	statistic_old = Math_GetStatistic(DrvPtr);

	/* pause clock and try some operation */
	(void)Math_PauseClock(DrvPtr);
	(void)Math_DoComputation(DrvPtr,0x3fff, 0x1);
	
	/* check results not changed */
	Xil_AssertNonvoid(Math_GetResult(DrvPtr)    == result_old);
	Xil_AssertNonvoid(Math_GetStatistic(DrvPtr) == statistic_old);
	
	/* resume clock */
	(void)Math_ResumeClock(DrvPtr);
	
	return XST_SUCCESS;
}
