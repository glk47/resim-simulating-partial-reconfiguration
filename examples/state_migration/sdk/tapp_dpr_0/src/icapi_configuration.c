/****************************************************************************
*
* Porject:     State Migration Application
* Filename:    icapi_configuration.c
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

#define READ_FRAME_HEADER_SIZE    32

#define DESYNC_COMMAND_SIZE       7 /* Number of words in the Desync command */
#define CAPTURE_COMMAND_SIZE      7 /* Number of words in the Capture command */
#define READ_CFG_REG_COMMAND_SIZE 6 /* Num of words in Read Config command */

/**************************** Type Definitions ******************************/


/***************** Macros (Inline Functions) Definitions ********************/


/************************** Variable Definitions ****************************/


/************************** Function Prototypes *****************************/

/****************************************************************************/
/**
* Icapi_ReadCfgFrames()
* 
*     Reads/Writes one frame from the FPGA and puts it in memory buffer 
*     specified by the user.
*
*     Note, user need to pass a buffer at least twice the size of a complete
*     frame because the FPGA device returns a Pad Frame (all zero) before
*     the actural frame data.
*
*****************************************************************************/

int Icapi_ReadCfgFrames(u32 FrameAddress, u32 *FrameBuffer) {

	int Status;
	u32 Index = 0;
	u32 WriteBuffer[READ_FRAME_HEADER_SIZE];

	Xil_AssertNonvoid(FrameBuffer != NULL);

	WriteBuffer[Index++] = XHI_DUMMY_PACKET;
	WriteBuffer[Index++] = XHI_SYNC_PACKET;
	WriteBuffer[Index++] = XHI_NOOP_PACKET;
	WriteBuffer[Index++] = XHI_NOOP_PACKET;

	WriteBuffer[Index++] = XHwIcap_Type1Write(XHI_CMD) | 1;
	WriteBuffer[Index++] = XHI_CMD_RCRC;
	WriteBuffer[Index++] = XHI_NOOP_PACKET;
	WriteBuffer[Index++] = XHI_NOOP_PACKET;

	/*
	 * Setup FAR, Setup CMD: RCFG
	 * 
	 * ReSim do not allow any NOP packets BETWEEN header and data, whereas on real FPGAs addtional
	 * NOP packets are inserted when switching the ICAP from write mode to read mode.
	 *
	 * Meanwhile, ReSim has a different FAR field composition from real FPGAs. Although we use
	 * Row & ColumnAddress here, they will actually be parameterized with RRid & RMid, and the 
	 * Top & Block parameter are fixed to zero.
	 * 
	 */
#if XHI_FAMILY == XHI_DEV_RESIM 
	/* ReSim */
	WriteBuffer[Index++] = XHwIcap_Type1Write(XHI_CMD) | 1;
	WriteBuffer[Index++] = XHI_CMD_RCFG;
	
	WriteBuffer[Index++] = XHwIcap_Type1Write(XHI_FAR) | 1;
	WriteBuffer[Index++] = FrameAddress;
#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V4) || (XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
	/* Virtex4 or Virtex5 or Virtex6 */
	WriteBuffer[Index++] = XHwIcap_Type1Write(XHI_CMD) | 1;
	WriteBuffer[Index++] = XHI_CMD_RCFG;
	WriteBuffer[Index++] = XHI_NOOP_PACKET;
	WriteBuffer[Index++] = XHI_NOOP_PACKET;
	WriteBuffer[Index++] = XHI_NOOP_PACKET;

	WriteBuffer[Index++] = XHwIcap_Type1Write(XHI_FAR) | 1;
	WriteBuffer[Index++] = FrameAddress;
#endif

	/*
	 * Setup FDRO: Create a Type 1 multi-word packet
	 * 
	 * The frame will be preceeded by a pad frame, and we need to one pad word for V4/V5/V6 devices.
	 * The definition of XHI_NUM_FRAME_AND_PAD_FRAME_WORDS is different between ReSim and the real device.
	 */
	WriteBuffer[Index++] = XHwIcap_Type1Read(XHI_FDRO) | XHI_NUM_FRAME_AND_PAD_FRAME_WORDS;
#if XHI_FAMILY == XHI_DEV_RESIM /* ReSim */

#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V4) || (XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
	WriteBuffer[Index++] = XHI_NOOP_PACKET;
	WriteBuffer[Index++] = XHI_NOOP_PACKET;
#endif

	/*
	 * Write the header to ICAP
	 * Read the frame of the data including the NULL frame.
	 */
	Status = Icapi_DoConfiguration(ICAPI_OP_WrCfg, (u32 *)&WriteBuffer[0], Index);
	if (Status != XST_SUCCESS)  {
		return XST_FAILURE;
	}

	Status = Icapi_DoConfiguration(ICAPI_OP_RdCfg, FrameBuffer, XHI_NUM_FRAME_AND_PAD_FRAME_WORDS);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Send DESYNC command
	 */
	Status = Icapi_GenDesync();
	if (Status != XST_SUCCESS)  {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
};

/****************************************************************************/
/**
* Icapi_CaptureFfBram()
* 
*     r - value read from or write to the target FF/BRAM
*     ll - logic allocation definition data structure of the FF/BRAM
*
*****************************************************************************/

int Icapi_CaptureFfBram(u32* r, CfgStateLl_t* ll) {

	int Status;
	int i,j;
	u32 FrameBuffer[XHI_NUM_FRAME_AND_PAD_FRAME_WORDS];
	
	*r = 0;
	for (j=0;j<ll->num;j++) { // loop through each frame
		CfgOneFrame_t* oft = &(ll->oft_l[j]);
		CfgOneBit_t* obt = oft -> obt_l;
		u32 frame_address = oft->addr;
		u32 num_of_bits = oft->num;

		Status = Icapi_ReadCfgFrames(frame_address, FrameBuffer);
		if (Status != XST_SUCCESS) {
			return XST_FAILURE;
		}

		for (i=0;i<num_of_bits;i++){ // loop through each INT0/INT1 bit in a frame

			// The bit organization in each frame is "little endian". i.e., the MSbit of
			// a word has an offset 31.

			u32 bit_offt = obt[i].offt & 0x1f;

#if XHI_FAMILY == XHI_DEV_RESIM /* ReSim */

			u32 word_indx = ((obt[i].offt) >> 5);
			u32 word_read = FrameBuffer[word_indx];

#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V4) || (XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
			// V4/V5/V6: For readback using Icapi_ReadCfgFrames(), the API returns a pad
			// frame before the actual frame data. So the word_indx has a constant offset.

			u32 word_indx = XHI_NUM_FRAME_WORDS + ((obt[i].offt) >> 5);
			u32 word_read = FrameBuffer[word_indx];

#endif


			u32 bit_pos = obt[i].pos;
#if XHI_FAMILY == XHI_DEV_RESIM /* ReSim */
			u32 bit = ((word_read >> bit_offt)) & 0x1;
#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V4) || (XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
			// V4/V5/V6: A "ZERO" in the frame data represent a "ONE" in
			// the user logic.

			u32 bit = (~(word_read >> bit_offt)) & 0x1;
#endif

			// Extract the bit from the frame and left shift it to the correct bit
			// postion of the readback register.

			*r |= (bit << bit_pos);
		}

	}

	return XST_SUCCESS;

}

/****************************************************************************/
/**
* Icapi_GenDesync()
*
*     Sends a DeSync command to the ICAP port. This command disables the 
*     ICAP port and ends (until a new Sync Word is sent).
*
* Icapi_GenCapture()
*
*     Sends a CAPTURE command to the ICAP port. This command captures all
*     of the flip flop values and copies them to the INT0/INT1 bit of the 
*     configuration memory.
*
*****************************************************************************/

int Icapi_GenDesync() {
	int Status;
	u32 FrameBuffer[DESYNC_COMMAND_SIZE];
	u32 Index =0;

	FrameBuffer[Index++] = (XHwIcap_Type1Write(XHI_CMD) | 1);
	FrameBuffer[Index++] = XHI_CMD_DESYNCH;
	FrameBuffer[Index++] = XHI_DUMMY_PACKET;
	FrameBuffer[Index++] = XHI_DUMMY_PACKET;

	Status = Icapi_DoConfiguration(ICAPI_OP_WrCfg, &FrameBuffer[0], Index);
	if (Status != XST_SUCCESS)  {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

int Icapi_GenCapture() {
	int Status;
	u32 FrameBuffer[CAPTURE_COMMAND_SIZE];
	u32 Index =0;

	FrameBuffer[Index++] = XHI_DUMMY_PACKET;
	FrameBuffer[Index++] = XHI_SYNC_PACKET;
#if ((XHI_FAMILY == XHI_DEV_FAMILY_V4) || (XHI_FAMILY == XHI_DEV_RESIM)) 
	/* Virtex4 or ReSim */

#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
	/* Virtex5 or Virtex6 */
	FrameBuffer[Index++] = XHI_NOOP_PACKET;
#endif
	FrameBuffer[Index++] = (XHwIcap_Type1Write(XHI_CMD) | 1);
	FrameBuffer[Index++] = XHI_CMD_GCAPTURE;
	FrameBuffer[Index++] =  XHI_DUMMY_PACKET;
	FrameBuffer[Index++] =  XHI_DUMMY_PACKET;

	Status = Icapi_DoConfiguration(ICAPI_OP_WrCfg, &FrameBuffer[0], Index);
	if (Status != XST_SUCCESS)  {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/****************************************************************************/
/**
 * Icapi_GetCfgReg()
 *
 *     This function returns the value of the specified ICAP configuration register.
 *     e.g., XHI_IDCODE, XHI_FLR.
 *
 *****************************************************************************/
 
int Icapi_GetCfgReg(u32 ConfigReg, u32 *RegData) {
	int Status;
	u32 FrameBuffer[READ_CFG_REG_COMMAND_SIZE];
	u32 Index =0;

	FrameBuffer[Index++] = XHI_DUMMY_PACKET;
	FrameBuffer[Index++] = XHI_SYNC_PACKET;
	FrameBuffer[Index++] = XHI_NOOP_PACKET;
	FrameBuffer[Index++] = XHI_NOOP_PACKET;
	
	/*
	 * ReSim do not allow any NOP packets BETWEEN header and data, whereas on real FPGAs addtional
	 * NOP packets are inserted when switching the ICAP from write mode to read mode.
	 */
	FrameBuffer[Index++] = XHwIcap_Type1Read(ConfigReg) | 0x1;
#if XHI_FAMILY == XHI_DEV_RESIM /* ReSim */

#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V4) || (XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
	FrameBuffer[Index++] = XHI_NOOP_PACKET;
#endif

	/*
	 * Write the header to the ICAP and read the configuration data from the ICAP
	 */
	Status = Icapi_DoConfiguration(ICAPI_OP_WrCfg, &FrameBuffer[0], Index);
	if (Status != XST_SUCCESS)  {
		return XST_FAILURE;
	}

	Status = Icapi_DoConfiguration(ICAPI_OP_RdCfg, RegData, 1);
	if (Status != XST_SUCCESS)  {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}


