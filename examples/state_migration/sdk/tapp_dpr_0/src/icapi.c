/****************************************************************************
*
* Porject:     State Migration Application
* Filename:    icapi.c
* Description: Software driver for XPS_ICAPI
* Date:        7 Mar. 2012
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xparameters.h"

#include "xil_io.h"
#include "icapi.h"
#include "icapi_configuration.h"

/************************** Constant Definitions ****************************/

#if XHI_FAMILY == XHI_DEV_RESIM
	/* ReSim */
#define ICAPI_RETRY_DELAY   0x80
#define ICAPI_MAX_RETRIES   0x80

#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V4) || (XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
	/* Virtex4 or Virtex5 or Virtex6*/
#define ICAPI_RETRY_DELAY   0x1000
#define ICAPI_MAX_RETRIES   0x1000

#endif

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

#define Icapi_GetRegister(RegOffset) \
	Xil_In32(DrvPtr->BaseAddress + (RegOffset))

#define Icapi_SetRegister(RegOffset, RegisterValue) \
	Xil_Out32(DrvPtr->BaseAddress + (RegOffset), (RegisterValue))
	
/************************** Variable Definitions ****************************/

static IcapiDriver_t* DrvPtr;

/************************** Function Prototypes *****************************/

/****************************************************************************/
/**
* Icapi_Initialize()
*
*    This function initializes a specific ICAPI instance. The IDCODE is
*    read from the FPGA and is checked with XHI_FPGA_IDCODE.
*
*****************************************************************************/

int Icapi_Initialize(IcapiDriver_t* Ptr, u32 BaseAddress) {
	
	int Status;
	u32 DeviceIdCode;
	
	DrvPtr = Ptr;
	
	DrvPtr->DeviceId = 0; /* Only alow one instance of ICAPI */
	DrvPtr->BaseAddress = BaseAddress;
	
	DrvPtr->BufferPtr = NULL;
	DrvPtr->BufferSize = 0;
	
	DrvPtr->CbHandler = (IcapiCbHandler_t) NULL;
	DrvPtr->CbRef = NULL;
	
	Icapi_SoftReset();

	/* 
	 * Read Device IDCODE
	 * 
	 * Dummy Read of the IDCODE as the first data read from the ICAP has to 
	 * be discarded (Due to the way the HW is designed). The seconde read
	 * reads the IDCODE and mask out the version section of the DeviceIdCode.
	 * 
	 */

	Status = Icapi_GetCfgReg(XHI_IDCODE, &DeviceIdCode);
	Status |= Icapi_GetCfgReg(XHI_IDCODE, &DeviceIdCode);
	Status |= Icapi_GenDesync();
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}
	DeviceIdCode = DeviceIdCode & XHI_DEVICE_ID_CODE_MASK;
	Xil_AssertNonvoid(DeviceIdCode == XHI_FPGA_IDCODE);
	DrvPtr->DeviceIdCode=XHI_FPGA_IDCODE;
	
	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Icapi_DoConfiguration()
*
*    This function writes the given user data to the ICAP port in polled mode. 
*    In particular, this function will write the specified number of words
*    into the ICAP port before returning.
*
* Icapi_DoConfigurationIntr()
*
*    This function writes the given user data to the ICAP port in the interrupt
*    mode. In particular, this function will pass the data pointer to the 
*    interrupt handler and enable the interrupt of the ICAPI. As the ICAPI is 
*    in IDLE state, it generates an interrupt immediately. The interrupt 
*    handler performs the subsequent operations to the ICAPI so as to transfer
*    all data in the buffer. 
*    
*    In order to use interrupts, it is necessary for the user to connect the driver
*    interrupt handler, Icapi_InterruptHandler(), to the interrupt driver. 
*
*****************************************************************************/

int Icapi_DoConfiguration(u32 Cfg, u32 *FrameBuffer, u32 NumWords) {

	unsigned int Retries = 0;
	
	Xil_AssertNonvoid(FrameBuffer != NULL);
	Xil_AssertNonvoid(NumWords > 0);

	/* check that the ICAP device is idle */
	if (Icapi_GetStatus() == ICAPI_IS_BUSY) { return XST_FAILURE; }
	
	/* check that the interrupt has been disabled */
	Xil_AssertNonvoid((Icapi_GetRegister(ICAPI_CTRL_OFFSET) & ICAPI_IER_IE_MASK) == 0x0);
	
	/* setup parameters and start transfer */
	Icapi_SetRegister(ICAPI_BADDR_OFFSET, (u32)FrameBuffer);
	Icapi_SetRegister(ICAPI_BSIZE_OFFSET, NumWords*4);
	Icapi_SetCfgStart(Cfg);

	/* wait until the current transfer finishes */
	while ( Icapi_GetStatus() == ICAPI_IS_BUSY ) {
		unsigned int RetryDelay = 0;
		while (RetryDelay < ICAPI_RETRY_DELAY)
			RetryDelay++;
		
		Retries++;
		if (Retries > ICAPI_MAX_RETRIES) {
			return XST_FAILURE;
		}
	}
	
	/* check result and return */
	if (Icapi_GetStatus() == ICAPI_IS_ERROR) {
		return XST_FAILURE;
	}
	return XST_SUCCESS;
}

int Icapi_DoConfigurationIntr(u32 Cfg, u32 *FrameBuffer, u32 NumWords) {
	
	Xil_AssertNonvoid(FrameBuffer != NULL);
	Xil_AssertNonvoid(NumWords > 0);

	/* check that the ICAP device is idle */
	if (Icapi_GetStatus() == ICAPI_IS_BUSY) { return XST_FAILURE; }
	
	/* setup parameters and start transfer */
	DrvPtr->BufferPtr=FrameBuffer;
	DrvPtr->BufferSize=NumWords;
	DrvPtr->CfgOp=Cfg;
	Icapi_SetIntrEnable(ICAPI_INTR_ENABLE);
	
	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Icapi_SoftReset()
* Icapi_GetStatus()
* Icapi_SetIntrEnable()
* Icapi_SetCfgStart()
* Icapi_SetCfgBufferAddress()
* Icapi_SetCfgBufferSize()
*
*****************************************************************************/

void Icapi_SoftReset() {
	Icapi_SetRegister(ICAPI_CTRL_OFFSET, 0x80000000);
}

u32 Icapi_GetStatus() {
	u32 stat_reg;
	
	stat_reg = Icapi_GetRegister(ICAPI_STAT_OFFSET);
	return ((stat_reg & ICAPI_STAT_STATE_MASK) >> ICAPI_STAT_STATE_SHIFT);
}

void Icapi_SetIntrEnable(u32 En) {
	u32 ier_reg;
	
	ier_reg = Icapi_GetRegister(ICAPI_IER_OFFSET);
	ier_reg = 
		(ier_reg & ~ICAPI_IER_IE_MASK) | 
		((En<<ICAPI_IER_IE_SHIFT) & ICAPI_IER_IE_MASK);
	
	Icapi_SetRegister(ICAPI_IER_OFFSET, ier_reg);
}

void Icapi_SetCfgStart(u32 Cfg) {
	u32 ctrl_reg;
	
	ctrl_reg = Icapi_GetRegister(ICAPI_CTRL_OFFSET);
	ctrl_reg = 
		(ctrl_reg & ~ICAPI_CTRL_OP_MASK) | 
		((Cfg<<ICAPI_CTRL_OP_SHIFT) & ICAPI_CTRL_OP_MASK);
	
	ctrl_reg |= 0x1; /* set ctrl_reg.start to trigger reconfiguration */
	
	Icapi_SetRegister(ICAPI_CTRL_OFFSET, ctrl_reg);
}

void Icapi_SetCfgBistreamAddress(u32 BistreamAddress) {
	Icapi_SetRegister(ICAPI_BADDR_OFFSET, BistreamAddress);
}

void Icapi_SetCfgBistreamSize(u32 BistreamSize) {
	Icapi_SetRegister(ICAPI_BSIZE_OFFSET, BistreamSize);
}

/****************************************************************************/
/**
* Icapi_SetCbHandler()
*
*     Sets the status callback function, the status handler, which the driver calls
*     when it encounters conditions that should be reported to the higher layer
*     software. The handler executes in an interrupt context, so it must minimize
*     the amount of processing performed such as transferring data to a thread 
*     context. 
*
*     FuncPtr: is the pointer to the callback function.
*     
*     CallBackRef: callback reference passed in by the application layer when 
*         setting the callback functions, and passed back to the upper layer 
*         when the callback is invoked.
* 
* Icapi_InterruptHandler()
*
*     The interrupt handler for ICAPI interrupts. This function must be connected
*     by the user to an interrupt source.
*
*     The interrupts are typically being used when writing data to the ICAP port
*     The reading of ICAP port is typically done in polled mode, altough interrupt
*     mode is also supported. 
*
*****************************************************************************/

void Icapi_SetCbHandler(IcapiCbHandler_t FuncPtr, void* CallBackRef) {
	Xil_AssertVoid(FuncPtr != NULL);

	DrvPtr->CbHandler = FuncPtr;
	DrvPtr->CbRef = CallBackRef;
}

void Icapi_InterruptHandler(IcapiDriver_t* Ptr) {
	Xil_AssertVoid(Ptr == DrvPtr);

	Icapi_SetIntrEnable(ICAPI_INTR_DISABLE);
	
	if(DrvPtr->BufferSize!=0) { /* start a new transfer */
		
		/* check that the ICAP device is idle */
		if (Icapi_GetStatus() == ICAPI_IS_BUSY) {
			DrvPtr->CbHandler(DrvPtr->CbRef, Icapi_GetStatus());
			return;
		}
		
		/* setup parameters and start transfer */
		Icapi_SetRegister(ICAPI_BADDR_OFFSET, (u32)(DrvPtr->BufferPtr));
		Icapi_SetRegister(ICAPI_BSIZE_OFFSET, (DrvPtr->BufferSize)*4);
		
		DrvPtr->BufferPtr = NULL;
		DrvPtr->BufferSize = 0;
		
		Icapi_SetCfgStart(DrvPtr->CfgOp);
		Icapi_SetIntrEnable(ICAPI_INTR_ENABLE);
		
	} else { /* finish the previous transfer */
		
		Icapi_SetIntrEnable(ICAPI_INTR_DISABLE);
		DrvPtr->CbHandler(DrvPtr->CbRef, Icapi_GetStatus());
	}
	
}
