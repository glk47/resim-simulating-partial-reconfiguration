#!/usr/bin/python
import sys
import os.path
import binascii

def str2ul(my_str):
    if   my_str.startswith('0x'): return int(my_str[2:],16)
    elif my_str.startswith('0b'): return int(my_str[2:],2)
    else                        : return int(my_str[0:],10)
    
# command-line arguments
# python $RSV_HOME/scripts/rsvsbt_memory.py $gra_ $edi_ $fsbt_ $addr_ $fmem_l
if len(sys.argv) > 5:
    gra = str2ul(sys.argv[1]) # granularity = 1,2,4,8
    edi = sys.argv[2]         # endian = le,be
    nbk = len(sys.argv[5:])   # number_of_banck = 1,2,4,8
    startaddr = int(str2ul(sys.argv[4]) / nbk)
    fsbt = open(sys.argv[3], "rb")
    fmem = []
    for fname in sys.argv[5:]:
        f = open(fname, "a");
        fmem.append(f)
else:
    print("[ERROR] Wrong number of arguments!!!\n")
    print("[ERROR] rsvsbt_memory $gra $endian $sbtfile $memfile [$memfile ...] !!!\n")
    sys.exit();

# open files
for f in fmem:
    print >> f, "@" + hex(startaddr)[2:]
    
# converting
is_eof  = 0 # end of file
my_totl = 0
while not(is_eof):
    
    # in each loop, write 1 line (32 bytes) of data to each bank of memory file 
    # so there are nbk * 32 bytes of data in all (was "num_byte = nbk * gra")
    num_byte = nbk * 32 
    
    my_buff = fsbt.read( num_byte )
    my_cont = len(my_buff)
    if( my_cont < num_byte ):
        # end of file reached
        is_eof = 1

        # add zeros to make "nbk * 32byte" aligned, 
        # note this is only needed at the end of the input sbt file. 
        # note my_cont == nbk * 32 at the end of this loop
        my_more = (num_byte - my_cont%num_byte)%num_byte
        for i in range(0,my_more):
            my_buff += chr(0)
            my_cont += 1
                
    my_totl = my_totl+my_cont           # my_cont == nbk * 32
    my_buff = binascii.hexlify(my_buff) # my_buff is a string of the desired hex digits
    
    # by default, sbt is big endian
    # convert to little endian if required
    if edi == "le":
        my_buff_be = my_buff
        my_buff_le = ""
        for i in range(0,my_cont/4): 
            my_word_be = my_buff_be[i*8:(i+1)*8] # conversion is word by word = 8 digits = 4 bytes
            my_word_le = my_word_be[6:8] + my_word_be[4:6] + my_word_be[2:4] + my_word_be[0:2]
            my_buff_le = my_buff_le + my_word_le
        my_buff = my_buff_le
    
    # write 4 spaces to the beginning of each line
    for f in fmem:
        f.write("    "); 
    
    # write 1 line (nbk * 32 bytes) of sbt data to the memory file
    # the inner loop is looping through each bank, the outer loop
    # goes through 32/granularity times
    for j in range(0,32/gra):
        for i, f in enumerate(fmem):
            index = i+nbk*j
            f.write( my_buff[index*gra*2:(index+1)*gra*2] ); f.write(" ");
            
    # write \n to the end of each line
    for f in fmem:
        f.write("\n"); 

# close files
fsbt.close();
for f in fmem:
    f.write("\n"); 
    f.close();

print ""



