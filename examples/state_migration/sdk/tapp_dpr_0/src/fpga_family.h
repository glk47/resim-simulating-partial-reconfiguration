/****************************************************************************
*
* Porject:     State Migration Application
* Filename:    fpga_family.h
* Description: Software driver for XPS_ICAPI
* Date:        7 Mar. 2012
*
*****************************************************************************/

#ifndef __FPGA_FAMILIY_H__
#define __FPGA_FAMILIY_H__

#ifdef __cplusplus
extern "C" {
#endif

/** @name FPGA Family for ReSim/Virtex4/Virtex5/Virtex6
 *
 * @{
 */
 
#define XHI_DEV_RESIM           0  /* ReSim */
#define XHI_DEV_FAMILY_V4       4  /* Virtex4 */
#define XHI_DEV_FAMILY_V5       5  /* Virtex5 */
#define XHI_DEV_FAMILY_V6       6  /* Virtex6 */

/* @} */

/** @name IDCODE for ReSim/Virtex4/Virtex5/Virtex6
 *
 * @{
 */

#define XHI_RESIM_1_00A 0x0c1b2011

#define XHI_RESIM_NUM_DEVICES  1

#define XHI_XC4VLX15    0x01658093
#define XHI_XC4VLX25    0x0167C093
#define XHI_XC4VLX40    0x016A4093
#define XHI_XC4VLX60    0x016B4093
#define XHI_XC4VLX80    0x016D8093
#define XHI_XC4VLX100   0x01700093
#define XHI_XC4VLX160   0x01718093
#define XHI_XC4VLX200   0x01734093

#define XHI_XC4VSX25    0x02068093
#define XHI_XC4VSX35    0x02088093
#define XHI_XC4VSX55    0x020B0093

#define XHI_XC4VFX12    0x01E58093
#define XHI_XC4VFX20    0x01E64093
#define XHI_XC4VFX40    0x01E8C093
#define XHI_XC4VFX60    0x01EB4093
#define XHI_XC4VFX100   0x01EE4093
#define XHI_XC4VFX140   0x01F14093

#define XHI_V4_NUM_DEVICES  17

#define XHI_XC5VLX30    0x0286E093
#define XHI_XC5VLX50    0x02896093
#define XHI_XC5VLX85    0x028AE093
#define XHI_XC5VLX110   0x028D6093
#define XHI_XC5VLX220   0x0290C093
#define XHI_XC5VLX330   0x0295C093

#define XHI_XC5VLX30T   0x02A6E093
#define XHI_XC5VLX50T   0x02A96093
#define XHI_XC5VLX85T   0x02AAE093
#define XHI_XC5VLX110T  0x02AD6093
#define XHI_XC5VLX220T  0x02B0C093
#define XHI_XC5VLX330T  0x02B5C093

#define XHI_XC5VSX35T   0x02E72093
#define XHI_XC5VSX50T   0x02E9A093
#define XHI_XC5VSX95T   0x02ECE093

#define XHI_XC5VFX30T   0x03276093
#define XHI_XC5VFX70T   0x032C6093
#define XHI_XC5VFX100T  0x032D8093
#define XHI_XC5VFX130T  0x03300093
#define XHI_XC5VFX200T  0x03334093

#define XHI_V5_NUM_DEVICES  20

#define XHI_XC6VHX250T  0x042A2093
#define XHI_XC6VHX255T  0x042A4093
#define XHI_XC6VHX380T  0x042A8093
#define XHI_XC6VHX565T  0x042AC093

#define XHI_XC6VLX75T   0x04244093
#define XHI_XC6VLX130T  0x0424A093
#define XHI_XC6VLX195T  0x0424C093
#define XHI_XC6VLX240T  0x04250093
#define XHI_XC6VLX365T  0x04252093
#define XHI_XC6VLX550T  0x04256093
#define XHI_XC6VLX760   0x0423A093
#define XHI_XC6VSX315T  0x04286093
#define XHI_XC6VSX475T  0x04288093

#define XHI_V6_NUM_DEVICES  13

/* @} */

#define XHI_FAMILY      XHI_DEV_RESIM   //// XHI_DEV_RESIM XHI_DEV_FAMILY_V5
#define XHI_FPGA_IDCODE XHI_RESIM_1_00A //// XHI_RESIM_1_00A XHI_XC5VFX70T

#ifdef __cplusplus
}
#endif

#endif
