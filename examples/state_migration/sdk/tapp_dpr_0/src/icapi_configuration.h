/****************************************************************************
*
* Porject:     State Migration Application
* Filename:    icapi_configuration.h
* Description: Software driver for XPS_ICAPI
* Date:        7 Mar. 2012
*
*****************************************************************************/

#ifndef __ICAPI_CONFIGURATION_H__
#define __ICAPI_CONFIGURATION_H__

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "fpga_family.h"

/************************** Constant Definitions ****************************/

/**
 * @name Configuration Type1/Type2 packet headers masks
 * @{
 */
#define XHI_TYPE_MASK           0x7
#define XHI_REGISTER_MASK       0x1F
#define XHI_OP_MASK             0x3

#define XHI_WORD_COUNT_MASK_TYPE_1  0x7FF
#define XHI_WORD_COUNT_MASK_TYPE_2  0x07FFFFFF

#define XHI_TYPE_SHIFT          29
#define XHI_REGISTER_SHIFT      13
#define XHI_OP_SHIFT            27

#define XHI_TYPE_1              1
#define XHI_TYPE_2              2
#define XHI_OP_WRITE            2
#define XHI_OP_READ             1

/* @} */

/*
 * @name Addresses of the Configuration Registers
 * @{
 */
#define XHI_FAR             1
#define XHI_FDRI            2
#define XHI_FDRO            3
#define XHI_CMD             4
#define XHI_IDCODE          12

#define XHI_CRC             0
#define XHI_CTL             5
#define XHI_MASK            6
#define XHI_STAT            7
#define XHI_LOUT            8
#define XHI_COR             9
#define XHI_MFWR            10
#define XHI_CBC             11
#define XHI_AXSS            13

#if XHI_FAMILY == XHI_DEV_RESIM
	/*
	 * ReSim:
	 *    Note that only FAR, CMD, FDRI/O, IDCODE are supported
	 *    Other registers are treated as normal registers which won't respond
	 *    to any data written to them
	 */
#define XHI_NUM_REGISTERS   32

#elif XHI_FAMILY == XHI_DEV_FAMILY_V4
	/* Virtex4 */
#define XHI_NUM_REGISTERS   14

#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
	/* Virtex5 or Virtex6 */
#define XHI_C0R_1           14
#define XHI_CSOB            15
#define XHI_WBSTAR          16
#define XHI_TIMER           17
#define XHI_BOOTSTS         22
#define XHI_CTL_1           24
#define XHI_NUM_REGISTERS   25 /* Note that the register numbering is not sequential */

#endif
/* @} */

/**
 * @name Frame Address Register mask(s) and constant(s)
 * @{
 */
#if XHI_FAMILY == XHI_DEV_RESIM
	/* ReSim */
#define XHI_FAR_RRID_MASK           0xFF
#define XHI_FAR_RMID_MASK           0xFF
#define XHI_FAR_MINOR_ADDR_MASK     0xFFFF

#define XHI_FAR_RRID_SHIFT          24
#define XHI_FAR_RMID_SHIFT          16
#define XHI_FAR_MINOR_ADDR_SHIFT    0

#define XHI_FAR_CLB_BRAM_BLOCK      0 /**< CLB/IO/CLK/BRAM Block */
#define XHI_FAR_MASK_BLOCK          0xFF /**< Mask Block */

#elif XHI_FAMILY == XHI_DEV_FAMILY_V4
	/* Virtex4 */
#define XHI_FAR_BLOCK_MASK          0x7
#define XHI_FAR_TOP_BOTTOM_MASK     0x1
#define XHI_FAR_ROW_ADDR_MASK       0x1F
#define XHI_FAR_COLUMN_ADDR_MASK    0xFF
#define XHI_FAR_MINOR_ADDR_MASK     0x3F

#define XHI_FAR_MAJOR_FRAME_MASK    0xFF
#define XHI_FAR_MINOR_FRAME_MASK    0xFF

#define XHI_FAR_BLOCK_SHIFT         19
#define XHI_FAR_TOP_BOTTOM_SHIFT    22
#define XHI_FAR_ROW_ADDR_SHIFT      14
#define XHI_FAR_COLUMN_ADDR_SHIFT   6
#define XHI_FAR_MINOR_ADDR_SHIFT    0

#define XHI_FAR_MAJOR_FRAME_SHIFT   17
#define XHI_FAR_MINOR_FRAME_SHIFT   9

#define XHI_FAR_CLB_BLOCK           0 /**< CLB/IO/CLK Block */
#define XHI_FAR_BRAM_BLOCK          1 /**< Block RAM interconnect */
#define XHI_FAR_BRAM_INT_BLOCK      2 /**< Block RAM content */
#define XHI_FAR_MASK_BLOCK          3 /**< Mask Block */

#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
	/* Virtex5 or Virtex6 */
#define XHI_FAR_BLOCK_MASK          0x7
#define XHI_FAR_TOP_BOTTOM_MASK     0x1
#define XHI_FAR_ROW_ADDR_MASK       0x1F
#define XHI_FAR_COLUMN_ADDR_MASK    0xFF
#define XHI_FAR_MINOR_ADDR_MASK     0x7F

#define XHI_FAR_MAJOR_FRAME_MASK    0xFF
#define XHI_FAR_MINOR_FRAME_MASK    0xFF

#define XHI_FAR_BLOCK_SHIFT         21
#define XHI_FAR_TOP_BOTTOM_SHIFT    20
#define XHI_FAR_ROW_ADDR_SHIFT      15
#define XHI_FAR_COLUMN_ADDR_SHIFT   7
#define XHI_FAR_MINOR_ADDR_SHIFT    0

#define XHI_FAR_MAJOR_FRAME_SHIFT   17
#define XHI_FAR_MINOR_FRAME_SHIFT   9

#define XHI_FAR_CLB_BLOCK           0 /**< CLB/IO/CLK Block */
#define XHI_FAR_BRAM_BLOCK          1 /**< Block RAM content */
#define XHI_FAR_MASK_BLOCK          2 /**< Mask Block */

#endif
/* @} */

/**
 * @name Device ID Register mask(s) and constant(s)
 * @{
 */
 
#define XHI_DEVICE_ID_CODE_MASK     0x0FFFFFFF

/* @} */

/**
 * @name Configuration Commands
 * @{
 */
 
#define XHI_CMD_NULL            0
#define XHI_CMD_WCFG            1
#define XHI_CMD_RCFG            4
#define XHI_CMD_GRESTORE        10
#define XHI_CMD_GCAPTURE        12
#define XHI_CMD_DESYNCH         13

#define XHI_CMD_MFW             2
#define XHI_CMD_DGHIGH          3
#define XHI_CMD_START           5
#define XHI_CMD_RCAP            6
#define XHI_CMD_RCRC            7
#define XHI_CMD_AGHIGH          8
#define XHI_CMD_SWITCH          9
#define XHI_CMD_SHUTDOWN        11

#if XHI_FAMILY == XHI_DEV_RESIM
	/*
	 * ReSim:
	 *    Note that only NULL, W/RCFG, GRESTORE, GCAPTURE, DESYNC are supported
	 *    Other commands are treated as NULL.
	 */

#elif XHI_FAMILY == XHI_DEV_FAMILY_V4
	/* Virtex4 */

#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
	/* Virtex5 or Virtex6 */
#define XHI_CMD_IPROG           15
#define XHI_CMD_CRCC            16
#define XHI_CMD_LTIMER          17

#endif

#define XHI_TYPE_2_READ         ((XHI_TYPE_2 << XHI_TYPE_SHIFT) | (XHI_OP_READ << XHI_OP_SHIFT))
#define XHI_TYPE_2_WRITE        ((XHI_TYPE_2 << XHI_TYPE_SHIFT) | (XHI_OP_WRITE << XHI_OP_SHIFT))

/* @} */

/**
 * @name Packet constants
 * @{
 */
 
#define XHI_SYNC_PACKET             0xAA995566
#define XHI_DUMMY_PACKET            0xFFFFFFFF
#define XHI_NOOP_PACKET             (XHI_TYPE_1 << XHI_TYPE_SHIFT)

#define XHI_DISABLED_AUTO_CRC       0x0000DEFC
#define XHI_DISABLED_AUTO_CRC_ONE   0x9876
#define XHI_DISABLED_AUTO_CRC_TWO   0xDEFC

#if (XHI_FAMILY == XHI_DEV_RESIM)
	/* ReSim */
#define XHI_NUM_FRAME_BYTES         16  /* Number of bytes in a frame */
#define XHI_NUM_FRAME_WORDS         4   /* Number of Words in a frame */
#define XHI_NUM_FRAME_AND_PAD_FRAME_WORDS  4 /* ReSim do not require any Pad Frame */

#define XHI_GCLK_FRAMES             0
#define XHI_IOB_FRAMES              0
#define XHI_DSP_FRAMES              0
#define XHI_CLB_FRAMES              4
#define XHI_BRAM_FRAMES             4
#define XHI_BRAM_INT_FRAMES         0

#elif (XHI_FAMILY == XHI_DEV_FAMILY_V4)
	/* Virtex4 or Virtex5 */
#define XHI_NUM_FRAME_BYTES         164  /* Number of bytes in a frame */
#define XHI_NUM_FRAME_WORDS         41   /* Number of Words in a frame */
#define XHI_NUM_FRAME_AND_PAD_FRAME_WORDS  82 /* Frame + Pad Frame, i.e, 2 Frames */

#define XHI_GCLK_FRAMES             3
#define XHI_IOB_FRAMES              30
#define XHI_DSP_FRAMES              21
#define XHI_CLB_FRAMES              22
#define XHI_BRAM_FRAMES             64
#define XHI_BRAM_INT_FRAMES         20

#elif (XHI_FAMILY == XHI_DEV_FAMILY_V5)
	/* Virtex4 or Virtex5 */
#define XHI_NUM_FRAME_BYTES         164  /* Number of bytes in a frame */
#define XHI_NUM_FRAME_WORDS         41   /* Number of Words in a frame */
#define XHI_NUM_FRAME_AND_PAD_FRAME_WORDS  82 /* Frame + Pad Frame, i.e, 2 Frames */

#define XHI_GCLK_FRAMES             4
#define XHI_IOB_FRAMES              54
#define XHI_DSP_FRAMES              28
#define XHI_CLB_FRAMES              36
#define XHI_BRAM_FRAMES             64
#define XHI_BRAM_INT_FRAMES         30

#elif XHI_FAMILY == XHI_DEV_FAMILY_V6
	/* Virtex6 */
#define XHI_NUM_FRAME_BYTES         324  /* Number of bytes in a frame */
#define XHI_NUM_FRAME_WORDS         81   /* Number of Words in a frame */
#define XHI_NUM_FRAME_AND_PAD_FRAME_WORDS  162 /* Frame + Pad Frame, i.e, 2 Frames */

#define XHI_GCLK_FRAMES             4    // lingkang: copied from V5
#define XHI_IOB_FRAMES              54   // lingkang: copied from V5
#define XHI_DSP_FRAMES              28   // lingkang: copied from V5
#define XHI_CLB_FRAMES              36   // lingkang: copied from V5
#define XHI_BRAM_FRAMES             64   // lingkang: copied from V5
#define XHI_BRAM_INT_FRAMES         30   // lingkang: copied from V5

#endif

/* @} */

/************************** Type Definitions ********************************/

/**************************** Type Definitions *******************************/


/***************** Macro (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
* XHwIcap_Type1Read()
* XHwIcap_Type2Read()
* XHwIcap_Type1Write()
* XHwIcap_Type2Write()
*
*     Generates a Bitstream Type 1/2 packet header that reads/writes 
*     the requested Configuration register.
*
*****************************************************************************/
#define XHwIcap_Type1Read(Register) \
	( (XHI_TYPE_1 << XHI_TYPE_SHIFT) | (Register << XHI_REGISTER_SHIFT) | \
	(XHI_OP_READ << XHI_OP_SHIFT) )

#define XHwIcap_Type2Read(Register) \
	( XHI_TYPE_2_READ | (Register << XHI_REGISTER_SHIFT))

#define XHwIcap_Type1Write(Register) \
	( (XHI_TYPE_1 << XHI_TYPE_SHIFT) | (Register << XHI_REGISTER_SHIFT) | \
	(XHI_OP_WRITE << XHI_OP_SHIFT) )

#define XHwIcap_Type2Write(Register) \
	( (XHI_TYPE_2 << XHI_TYPE_SHIFT) | (Register << XHI_REGISTER_SHIFT) | \
	(XHI_OP_WRITE << XHI_OP_SHIFT) )

/****************************************************************************/
/**
*
* Generates a Type 1 packet header that is written to the Frame Address
* Register (FAR) for a Virtex4/Virtex5/Virtex6 device.
*
* @param    Top - top (0) or bottom (1) half of device
* @param    Block - Address Block Type (CLB or BRAM address space)
* @param    Row - H Clock row
* @param    ColumnAddress - CLB or BRAM column (MajorAddress)
* @param    MinorAdderss - Frame within column
*
* @return   Type 1 packet header to write the FAR
*
* @note     None.
*
*****************************************************************************/
#if XHI_FAMILY == XHI_DEV_RESIM
	/* ReSim */
#define XHwIcap_SetupFarVirtex(DUMMY_0, DUMMY_1, RRID, RMID, MinorAddress)  \
	((RRID << XHI_FAR_RRID_SHIFT) |                \
	(RMID << XHI_FAR_RMID_SHIFT) |                 \
	(MinorAddress << XHI_FAR_MINOR_ADDR_SHIFT))

#define XHI_FAR_RRid(f_) (((f_) >> XHI_FAR_RRID_SHIFT) & XHI_FAR_RRID_MASK)
#define XHI_FAR_RMid(f_) (((f_) >> XHI_FAR_RMID_SHIFT) & XHI_FAR_RMID_MASK)
#define XHI_FAR_MnA(f_)  (((f_) >> XHI_FAR_MINOR_ADDR_SHIFT) & XHI_FAR_MINOR_ADDR_MASK)

#elif ((XHI_FAMILY == XHI_DEV_FAMILY_V4) || (XHI_FAMILY == XHI_DEV_FAMILY_V5) || (XHI_FAMILY == XHI_DEV_FAMILY_V6))
	/* Virtex4 or Virtex5 or Virtex6*/
#define XHwIcap_SetupFarVirtex(Top, Block, Row, ColumnAddress, MinorAddress)  \
	((Top << XHI_FAR_TOP_BOTTOM_SHIFT) |           \
	(Block << XHI_FAR_BLOCK_SHIFT) |               \
	(Row << XHI_FAR_ROW_ADDR_SHIFT) |              \
	(ColumnAddress << XHI_FAR_COLUMN_ADDR_SHIFT) | \
	(MinorAddress << XHI_FAR_MINOR_ADDR_SHIFT))

#define XHI_FAR_Top(f_) (((f_) >> XHI_FAR_TOP_BOTTOM_SHIFT) & XHI_FAR_TOP_BOTTOM_MASK)
#define XHI_FAR_Blk(f_) (((f_) >> XHI_FAR_BLOCK_SHIFT) & XHI_FAR_BLOCK_MASK)
#define XHI_FAR_Row(f_) (((f_) >> XHI_FAR_ROW_ADDR_SHIFT) & XHI_FAR_ROW_ADDR_MASK)
#define XHI_FAR_Col(f_) (((f_) >> XHI_FAR_COLUMN_ADDR_SHIFT) & XHI_FAR_COLUMN_ADDR_MASK)
#define XHI_FAR_MnA(f_) (((f_) >> XHI_FAR_MINOR_ADDR_SHIFT) & XHI_FAR_MINOR_ADDR_MASK)

#endif

/************************** Function Prototypes *****************************/

int Icapi_ReadCfgFrames(u32 FrameAddress, u32 *FrameBuffer);
int Icapi_CaptureFfBram(u32* r, CfgStateLl_t* ll);

int Icapi_GenDesync();
int Icapi_GenCapture();
int Icapi_GetCfgReg(u32 ConfigReg, u32 *RegData);

/************************** Variable Declarations ***************************/

#ifdef __cplusplus
}
#endif

#endif

