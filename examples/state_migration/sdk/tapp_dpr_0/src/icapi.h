/****************************************************************************
*
* Porject:     State Migration Application
* Filename:    icapi.h
* Description: Software driver for XPS_ICAPI
* Date:        7 Mar. 2012
*
*****************************************************************************/

#ifndef __ICAPI_H__
#define __ICAPI_H__

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "fpga_family.h"

/************************** Constant Definitions ****************************/

/******************************************************************/
/** @name Register Map
 *
 * Register offsets for the ICAPI device.
 * @{
 */
#define ICAPI_CTRL_OFFSET       0x00  /**< ICAPI Control Register */
#define ICAPI_STAT_OFFSET       0x04  /**< ICAPI Status Register */
#define ICAPI_BADDR_OFFSET      0x08  /**< Bitstream Address Register */
#define ICAPI_BSIZE_OFFSET      0x0c  /**< Bitstream Size */
#define ICAPI_IER_OFFSET        0x10  /**< ICAPI Interrupt Enable Register */

/* @} */


/** @name Register bits definitions
 *
 * @{
 */

#define ICAPI_CTRL_RST_MASK     0x80000000 // Reset
#define ICAPI_CTRL_OP_MASK      0x00000002 // 0:RdCfg, 1:WrCfg
#define ICAPI_CTRL_START_MASK   0x00000001 // Start operation (write-only)
#define ICAPI_STAT_STATE_MASK   0x00000003 // ICAPI status (reset by writing ICAPI_START)
#define ICAPI_IER_IE_MASK       0x80000000 // Interrupt Enable

#define ICAPI_CTRL_RST_SHIFT    31
#define ICAPI_CTRL_OP_SHIFT     1
#define ICAPI_CTRL_START_SHIFT  0
#define ICAPI_STAT_STATE_SHIFT  0
#define ICAPI_IER_IE_SHIFT      31

#define ICAPI_INTR_ENABLE   0x1
#define ICAPI_INTR_DISABLE  0x0

#define ICAPI_OP_RdCfg  0x0
#define ICAPI_OP_WrCfg  0x1

#define ICAPI_IS_BUSY   0x0
#define ICAPI_IS_DONE   0x1
#define ICAPI_IS_ERROR  0x3

/* @} */

/**************************** Type Definitions ******************************/

/**
 * The ICAPI interrupt callback functional pointer. The user is required to
 * define a handler of this type and install such function to the driver by
 * calling Icapi_SetCbHandler(); Such user-defined callback function will
 * be called by the ICAPI interrupt handler so that the hanlder can report
 * interrupt-related events to the upper layer software. The callback function
 * executes in an interrupt context such that only minimal processing can be 
 * performed.
 *
 * CallBackRef: callback reference passed in by the application layer when 
 *     setting the callback functions, and passed back to the upper layer 
 *     when the callback is invoked.
 * IcapiStatus: the status of the ICAPI device, its up to the callback
 *     function whether to use this status or not.
 */
typedef void (*IcapiCbHandler_t) (void* CallBackRef, u32 IcapiStatus);
 
/**
 * The ICAPI driver instance data. The user is required to define a
 * variable of this type and pass a pointer of the driver instance to
 * the initialization function. Only one instance of ICAPI is allowed 
 * due to the way the FPGA is designed. 
 */
typedef struct {
	u32 DeviceId;               /**< Device ID: 0,1,2.... */
	u32 DeviceIdCode;           /**< Device ID: IDCode Register */
	u32 BaseAddress;            /**< Device base address */
	
	volatile int CfgOp;         /**< Reconfiguration operation */
	volatile u32 *BufferPtr;    /**< Buffer to write/read to the ICAP */
	volatile u32 BufferSize;    /**< Size (in words) of the buffer */
	
	IcapiCbHandler_t CbHandler; /**< Interrupt handler callback */
	void *CbRef;                /**< Callback ref. for the interrupt handler */

} IcapiDriver_t;

/**
 * The logic allocation (ll) data structure. It is used by two functions,
 * IcapI_CaptureFfBram() and IcapI_RestoreFfBram(), to save and restore 
 * FF,BRAM state via the configuration port. 
 * 
 * Typically, a register has multiple bits and each bit is mapped to one 
 * bit of a certain configuration frame of the FPGA fabric. Frame address 
 * and bit offset are required to locate one bit in the FPGA fabric.
 *
 * Users are required to construct and pass the required allocation 
 * information to the driver so as to capture or restore state data. 
 */
  
typedef struct {
	u32 pos;                    /**< Bit position within the user-defined register */
	u32 offt;                   /**< Bit offset within the configuration frame */
} CfgOneBit_t;

typedef struct {
	u32  addr;                  /**< Frame address, e.g. 0x00018300 */
	u32  num;                   /**< Number of bits in this frame */
	CfgOneBit_t* obt_l;         /**< A list of bits in this frame */
} CfgOneFrame_t;

typedef struct {
	u32 num;                    /**< Number of frames the register is distributed in */
	CfgOneFrame_t* oft_l;       /**< A list of frames for the register */
} CfgStateLl_t;                 

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Function Prototypes ******************************/

int Icapi_Initialize();

int Icapi_DoConfiguration(u32 Cfg, u32 *FrameBuffer, u32 NumWords);
int Icapi_DoConfigurationIntr(u32 Cfg, u32 *FrameBuffer, u32 NumWords);
void Icapi_SoftReset();
u32 Icapi_GetStatus();
void Icapi_SetIntrEnable(u32 En);
void Icapi_SetCfgStart(u32 Cfg);
void Icapi_SetCfgBistreamAddress(u32 BistreamAddress);
void Icapi_SetCfgBistreamSize(u32 BistreamSize);

void Icapi_SetCbHandler(IcapiCbHandler_t FuncPtr, void* CallBackRef);
void Icapi_InterruptHandler();

/************************** Variable Definitions *****************************/


#ifdef __cplusplus
}
#endif

#endif


