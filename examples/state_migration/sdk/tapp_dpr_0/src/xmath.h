/****************************************************************************
*
* Porject:     State Migration Application
* Filename:    xmath.h
* Description: Software driver for XPS_MATH
* Date:        7 Mar. 2012
*
*****************************************************************************/

#ifndef __XPS_MATH_H__
#define __XPS_MATH_H__

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xil_types.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

typedef struct {
	u16 DeviceId;               /**< Device ID */
	u32 BaseAddress;            /**< Device base address */

} MathDriver_t;

/***************** Macros (Inline Functions) Definitions ********************/

#define MATH_ADDER_ID       0xc001
#define MATH_MAXIMUM_ID     0xf00d

#define Math_GetId(DrvPtr)  (u16)((Math_GetStatistic(DrvPtr)) >> 16)
#define Math_GetCnt(DrvPtr) (u16)((Math_GetStatistic(DrvPtr)) >> 0 )

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

int Math_Initialize(MathDriver_t* DrvPtr, u32 DeviceId, u32 BaseAddress);
u32 Math_DoComputation(MathDriver_t* DrvPtr, u32 first, u32 second);

u32 Math_GetResult(MathDriver_t* DrvPtr);
u32 Math_GetStatistic(MathDriver_t* DrvPtr);

void Math_SoftReset(MathDriver_t* DrvPtr);
void Math_PauseClock(MathDriver_t* DrvPtr);
void Math_ResumeClock(MathDriver_t* DrvPtr);

int Math_TestComputation(MathDriver_t* DrvPtr, u32 first, u32 second);
int Math_TestReset(MathDriver_t* DrvPtr);
int Math_TestClock(MathDriver_t* DrvPtr);

#ifdef __cplusplus
}
#endif

#endif
