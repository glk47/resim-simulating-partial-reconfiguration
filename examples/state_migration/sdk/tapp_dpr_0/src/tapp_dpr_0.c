/****************************************************************************
*
* Porject:     State Migration Application
* Filename:    main.c
* Description: Main applicaiton
* Date:        7 Mar. 2012
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xparameters.h"

#include "xenv_standalone.h"
#include "xil_exception.h"

#include "xintc.h"
#include "xuartlite.h"

#include "xsysace.h"
#include "sysace_stdio.h"
#include "xmath.h"
#include "icapi.h"
#include "icapi_configuration.h"

#include "fpga_family.h"

/************************** Constant Definitions ****************************/

#if XHI_FAMILY == XHI_DEV_RESIM /* ReSim */

#elif (XHI_FAMILY == XHI_DEV_FAMILY_V5)
#define BOARD_ML507
#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V4) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
#error
#endif

#define RM_BUFF_SIZE_IN_BYTE  65536
#define RM_BUFF_SIZE_IN_WORD  (RM_BUFF_SIZE_IN_BYTE/4)

/**************************** Type Definitions ******************************/


/***************** Macros (Inline Functions) Definitions ********************/

#ifdef BOARD_ML507
#define Ml50x_PrintInfo(str) print(str);
#else
#define Ml50x_PrintInfo(str) 
#endif

#define Ml50x_LoopIfFalse(e_) if ((e_) == FALSE) { while (TRUE); }
#define Ml50x_ReturnIfFalse(e_) if ((e_) == FALSE) { return (XST_FAILURE); }

#ifdef BOARD_ML507
#define Ml50x_RETRY_DELAY   0x1000
#define Ml50x_MAX_RETRIES   0x1000
#else
#define Ml50x_RETRY_DELAY   0x80
#define Ml50x_MAX_RETRIES   0x80
#endif

/************************** Variable Definitions ****************************/

u32* rm0_buffer = (u32*) 0x40000;
u32* rm1_buffer = (u32*) 0x50000;
u32 rm0_size_in_word = 256;
u32 rm1_size_in_word = 256;

XSysAce SysAce;
SYSACE_FILE *stream;

IcapiDriver_t IcapiDrv;
MathDriver_t MathDrv;
XIntc IntcDrv;
XUartLite UartDrv;

#include "logic_allocation.h"

/************************** Function Prototypes *****************************/

int Ml50x_Initialize();
int Ml50x_Finalize();
int Ml50x_LoadMemBitstream(u32* rm_buffer, u32* rm_size_in_word, char* filename);
int Ml50x_SimpleDPR(int math_core);
int Ml50x_StateMigration();
int Ml50x_TrafficContention(int math_core);

void Ml50x_ConfigurationCbHandler (void* CallBackRef, u32 IcapiStatus);
void Ml50x_UartSendCbHandler (void* CallBackRef, unsigned int ByteCount);
void Ml50x_UartRecvCbHandler (void* CallBackRef, unsigned int ByteCount);

/****************************************************************************/
/**
* main()
*
*****************************************************************************/

int main() {

	XCACHE_DISABLE_ICACHE(); // For DMA: Memory coherence
	XCACHE_DISABLE_DCACHE(); // For DMA: Memory coherence

	Ml50x_PrintInfo("--------Entering main--------\n\r");
	
	Ml50x_PrintInfo("... Initializing ...");
	if (Ml50x_Initialize() == XST_SUCCESS){
		Ml50x_PrintInfo("PASSED\r\n");
	}else{
		Ml50x_PrintInfo("FAILED\r\n");
	}
	
	Ml50x_PrintInfo("... Running Ml50x_SimpleDPR() ...");
	if (Ml50x_SimpleDPR(MATH_MAXIMUM_ID) == XST_SUCCESS){
		Ml50x_PrintInfo("PASSED\r\n");
	}else{
		Ml50x_PrintInfo("FAILED\r\n");
	}
	
	Ml50x_PrintInfo("... Running Ml50x_StateMigration() ...");
	if (Ml50x_StateMigration() == XST_SUCCESS){
		Ml50x_PrintInfo("PASSED\r\n");
	}else{
		Ml50x_PrintInfo("FAILED\r\n");
	}

	Ml50x_PrintInfo("... Running Ml50x_TrafficContention() ...\r\n");
	if (Ml50x_TrafficContention(MATH_ADDER_ID) == XST_SUCCESS){
		Ml50x_PrintInfo("... PASSED\r\n");
	}else{
		Ml50x_PrintInfo("... FAILED\r\n");
	}
	
	Ml50x_PrintInfo("--------Exiting main--------\n\r");

	XCACHE_DISABLE_ICACHE();
	XCACHE_DISABLE_DCACHE();

	return 0;
}

/****************************************************************************/
/**
* Ml50x_Initialize()
* Ml50x_Finalize()
* Ml50x_LoadMemBitstream()
*
*****************************************************************************/

int Ml50x_Initialize() {

	int status;

#ifdef BOARD_ML507

	/* initialize systemace driver instance */
	
	status = XSysAce_Initialize(&SysAce, XPAR_SYSACE_0_DEVICE_ID);
	Xil_AssertNonvoid(status == XST_SUCCESS);
	
	/* load bitstream to memory */
	
	status = Ml50x_LoadMemBitstream(rm0_buffer, &rm0_size_in_word, "ML50x\\george\\adder.bin");
	status = Ml50x_LoadMemBitstream(rm1_buffer, &rm1_size_in_word, "ML50x\\george\\maximum.bin");
	
	/* check that bitstream has been correctly loaded */
	
	Xil_AssertNonvoid(rm0_buffer[0xc]==0xaa995566);Xil_AssertNonvoid(rm0_size_in_word == 15563);
	Xil_AssertNonvoid(rm1_buffer[0xc]==0xaa995566);Xil_AssertNonvoid(rm1_size_in_word == 15563);

#else

	/* bitstreams are loaded by the simulation environmen */
	
	/* check that bitstream has been correctly loaded */
	
	Xil_AssertNonvoid(rm0_buffer[0x0]==0xaa995566);Xil_AssertNonvoid(rm0_size_in_word == 256);
	Xil_AssertNonvoid(rm1_buffer[0x0]==0xaa995566);Xil_AssertNonvoid(rm1_size_in_word == 256);

#endif

	/* initialize xps_uartlite driver instance */
	
	status = XUartLite_Initialize(&UartDrv, XPAR_UARTLITE_0_DEVICE_ID);
	Xil_AssertNonvoid(status == XST_SUCCESS);
	XUartLite_SetRecvHandler(&UartDrv, Ml50x_UartSendCbHandler, (void*) NULL);
	XUartLite_SetSendHandler(&UartDrv, Ml50x_UartRecvCbHandler, (void*) NULL);
	
	/* initialize xps_icapi driver instance */
	
	status = Icapi_Initialize(&IcapiDrv, XPAR_XPS_ICAPI_0_MEM_BASEADDR);
	Xil_AssertNonvoid(status == XST_SUCCESS);
	Icapi_SetCbHandler(Ml50x_ConfigurationCbHandler, (void*) NULL);
	
	/* initialize xps_math driver instance */
	
	status = Math_Initialize(&MathDrv, 0, XPAR_XPS_MATH_0_BASEADDR);
	Xil_AssertNonvoid(status == XST_SUCCESS);
	
	/* initialize interrupt controller driver instance */
	
	Xil_ExceptionInit();
	Xil_ExceptionRegisterHandler(XIL_EXCEPTION_ID_NON_CRITICAL_INT,
			(Xil_ExceptionHandler)XIntc_InterruptHandler,
			(void*) &IntcDrv);
	Xil_ExceptionEnableMask(XIL_EXCEPTION_NON_CRITICAL);
	
	status = XIntc_Initialize(&IntcDrv,XPAR_INTC_0_DEVICE_ID);
	status |= XIntc_SetOptions(&IntcDrv, XIN_SVC_ALL_ISRS_OPTION);
	Xil_AssertNonvoid(status == XST_SUCCESS);
	
	status |= XIntc_Start(&IntcDrv, XIN_REAL_MODE);
	Xil_AssertNonvoid(status == XST_SUCCESS);
	
	/* connect and enable interrupt sources */
	
	status = XIntc_Connect(&IntcDrv, XPAR_XPS_INTC_0_XPS_ICAPI_0_IP2INTC_IRPT_INTR,
		(XInterruptHandler)Icapi_InterruptHandler, (void*) &IcapiDrv);
	status |= XIntc_Connect(&IntcDrv, XPAR_XPS_INTC_0_XPS_UART_0_INTERRUPT_INTR,
		(XInterruptHandler)XUartLite_InterruptHandler, (void*) &UartDrv);
	Xil_AssertNonvoid(status == XST_SUCCESS);
	
	XIntc_Enable(&IntcDrv, XPAR_XPS_INTC_0_XPS_ICAPI_0_IP2INTC_IRPT_INTR);
	XIntc_Enable(&IntcDrv, XPAR_XPS_INTC_0_XPS_UART_0_INTERRUPT_INTR);
	
	return XST_SUCCESS;
}

int Ml50x_Finalize() {
	return XST_SUCCESS;
}

int Ml50x_LoadMemBitstream(u32* rm_buffer, u32* rm_size_in_word, char* filename) {

	int status;
	u32 numCharsRead;
	
	/* Opening file */
	stream = sysace_fopen(filename, "r");
	Ml50x_ReturnIfFalse(stream != NULL);

	/* Read from systemAce to memory buffer */
	numCharsRead = sysace_fread((u8*)rm_buffer, 1, RM_BUFF_SIZE_IN_BYTE, stream);
	Ml50x_ReturnIfFalse(numCharsRead > 0);
	*rm_size_in_word = (u32)(numCharsRead / 4);

	/* Closing file */
	status = sysace_fclose(stream);
	Ml50x_ReturnIfFalse(status == XST_SUCCESS);

	return XST_SUCCESS;

}

/****************************************************************************/
/**
* Ml50x_SimpleDPR()
* Ml50x_StateMigration()
* Ml50x_TrafficContention()
*
*****************************************************************************/

int Ml50x_SimpleDPR(int math_core) {

	int status;
	u32* rm_buffer;
	u32 rm_size_in_word;

	/* do some computation */
	status = Math_TestComputation(&MathDrv,3,5);
	status |= Math_TestComputation(&MathDrv,0xffff,1);
	Ml50x_LoopIfFalse(status == XST_SUCCESS);

	/* do partial reconfiguration */
	if (math_core != Math_GetId(&MathDrv)){
		switch(math_core) {
			case MATH_ADDER_ID:
				rm_buffer = rm0_buffer;
				rm_size_in_word = rm0_size_in_word;
				break;
				
			case MATH_MAXIMUM_ID:
				rm_buffer = rm1_buffer;
				rm_size_in_word = rm1_size_in_word;
				break;
				
			default:
				return XST_FAILURE;
				break;
		}
		Xil_AssertNonvoid(rm_buffer!=NULL);
		Xil_AssertNonvoid(rm_size_in_word>0);
		
		status = Icapi_DoConfiguration(ICAPI_OP_WrCfg, rm_buffer, rm_size_in_word);
	}
	Math_SoftReset(&MathDrv);
	
	/* do some computation */
	status = Math_TestComputation(&MathDrv,3,5);
	status |= Math_TestComputation(&MathDrv,0xffff,1);
	Ml50x_LoopIfFalse(status == XST_SUCCESS);
	
	return XST_SUCCESS;
}

int Ml50x_StateMigration() {
	
	int status;
	u32 reg32read;
	CfgStateLl_t* result_ll_ptr;
	
	switch(Math_GetId(&MathDrv)) {
		case MATH_ADDER_ID: result_ll_ptr = &mca_result_ll; break;
		case MATH_MAXIMUM_ID: result_ll_ptr = &mcm_result_ll; break;
		default: return XST_FAILURE; break;
	}
	Xil_AssertNonvoid(result_ll_ptr!=NULL);
	
	/* do some computation and readback the "result" register */
	
	(void)Math_DoComputation(&MathDrv,0x0,0xff008421);
	status = Icapi_GenCapture();
	status |= Icapi_GenDesync();
	status |= Icapi_CaptureFfBram(&reg32read,result_ll_ptr);
	
	Ml50x_LoopIfFalse(status == XST_SUCCESS);
	Ml50x_LoopIfFalse(reg32read == 0xff008421);

	(void)Math_DoComputation(&MathDrv,0x842100ff,0x0);
	status = Icapi_GenCapture();
	status |= Icapi_GenDesync();
	status |= Icapi_CaptureFfBram(&reg32read,result_ll_ptr);
	
	Ml50x_LoopIfFalse(status == XST_SUCCESS);
	Ml50x_LoopIfFalse(reg32read == 0x842100ff);
	
	/* reset and readback the "result" register */
	
	Math_SoftReset(&MathDrv);
	status = Icapi_GenCapture();
	status |= Icapi_GenDesync();
	status |= Icapi_CaptureFfBram(&reg32read,result_ll_ptr);
	
	Ml50x_LoopIfFalse(status == XST_SUCCESS);
	Ml50x_LoopIfFalse(reg32read == 0x0);
	
	return XST_SUCCESS;
}

int Ml50x_TrafficContention(int math_core) {

	int status;
	u32* rm_buffer;
	u32 rm_size_in_word;
	
	unsigned int Retries = 0;

	/* do some computation */
	status = Math_TestComputation(&MathDrv,3,5);
	status |= Math_TestComputation(&MathDrv,0xffff,1);
	Ml50x_LoopIfFalse(status == XST_SUCCESS);

#ifdef BOARD_ML507
	xil_printf("BEFORE_RECON:0x%x,0x%x\r\n",Math_GetId(&MathDrv),Math_GetCnt(&MathDrv));
#endif

	/* do partial reconfiguration */
	if (math_core != Math_GetId(&MathDrv)){
		switch(math_core) {
			case MATH_ADDER_ID:
				rm_buffer = rm0_buffer;
				rm_size_in_word = rm0_size_in_word;
				break;
				
			case MATH_MAXIMUM_ID:
				rm_buffer = rm1_buffer;
				rm_size_in_word = rm1_size_in_word;
				break;
				
			default:
				return XST_FAILURE;
				break;
		}
		Xil_AssertNonvoid(rm_buffer!=NULL);
		Xil_AssertNonvoid(rm_size_in_word>0);
		
		status = Icapi_DoConfigurationIntr(ICAPI_OP_WrCfg, rm_buffer, rm_size_in_word);
	}
	
	/* 
	 * Wait for partial reconfiguration
	 * 
	 * Poll the Id && Cnt to wait for the end of partial reconfiguration.
	 * This is to demonstrate traffic contention between the application 
	 * and the bitstream transfer process. 
	 * 
	 */

#ifdef BOARD_ML507
	unsigned int Id=0xcccc;  // Initialize with some random value
	unsigned int Cnt=0xdddd; // Initialize with some random value
	while ( ((Id=Math_GetId(&MathDrv))!=math_core) || ((Cnt=Math_GetCnt(&MathDrv))!=0) ) {
#else
	while ( ((Math_GetId(&MathDrv))!=math_core) || ((Math_GetCnt(&MathDrv))!=0) ) {
#endif

#ifdef BOARD_ML507
		xil_printf("%d:0x%x,0x%x\r\n",Retries,Id,Cnt);
#endif
		unsigned int RetryDelay = 0;
		while (RetryDelay < Ml50x_RETRY_DELAY)
			RetryDelay++;
		
		Retries++;
		if (Retries > Ml50x_MAX_RETRIES) {
			return XST_FAILURE;
		}
	}

#ifdef BOARD_ML507
	xil_printf("%d:0x%x,0x%x\r\n",Retries,Id,Cnt);
	xil_printf("AFTER_RECON:0x%x,0x%x\r\n",Math_GetId(&MathDrv),Math_GetCnt(&MathDrv));
#endif

	/* do some computation */
	status = Math_TestComputation(&MathDrv,3,5);
	status |= Math_TestComputation(&MathDrv,0xffff,1);
	Ml50x_LoopIfFalse(status == XST_SUCCESS);
	
	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Ml50x_ConfigurationCbHandler()
* Ml50x_UartSendCbHandler()
* Ml50x_UartRecvCbHandler()
*
*****************************************************************************/

void Ml50x_ConfigurationCbHandler (void* CallBackRef, u32 IcapiStatus){
	
	if(IcapiStatus == ICAPI_IS_DONE)
		Math_SoftReset(&MathDrv);
}

void Ml50x_UartSendCbHandler (void* CallBackRef, unsigned int ByteCount){
	
}

void Ml50x_UartRecvCbHandler (void* CallBackRef, unsigned int ByteCount){
	
}

