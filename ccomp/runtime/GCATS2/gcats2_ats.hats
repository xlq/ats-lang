 #include "config.h"


 #ifndef GCATS2_ATS_HATS
 #define GCATS2_ATS_HATS
 #define NBIT_PER_BYTE 8
 #define NBIT_PER_BYTE_LOG 3
 #assert (NBIT_PER_BYTE == 1 << NBIT_PER_BYTE_LOG)
 #define NBIT_PER_BYTE_MASK (NBIT_PER_BYTE - 1)
 #if (SIZEOF_VOIDP * NBIT_PER_BYTE == 32)
 #define __WORDSIZE 32
 #endif
 #if (SIZEOF_VOIDP * NBIT_PER_BYTE == 64)
 #define __WORDSIZE 64
 #endif
 #print "__WORDSIZE = "; #print __WORDSIZE; #print "\n"
 #if (__WORDSIZE != 32)
 #if (__WORDSIZE != 64)
 #error "__WORDSIZE is neither 32 nor 64!\n"
 #endif
 #endif
 #define __PAGESIZE 4096
 #define NBIT_PER_WORD __WORDSIZE
 #if (__WORDSIZE == 32)
 #define NBIT_PER_WORD_LOG 5
 #define NBYTE_PER_WORD 4
 #define NBYTE_PER_WORD_LOG 2
 #endif
 #if (__WORDSIZE == 64)
 #define NBIT_PER_WORD_LOG 6
 #define NBYTE_PER_WORD 8
 #define NBYTE_PER_WORD_LOG 3
 #endif
 #assert (NBIT_PER_WORD == 1 << NBIT_PER_WORD_LOG)
 #assert (NBIT_PER_WORD == NBIT_PER_BYTE * NBYTE_PER_WORD)
 #assert (NBYTE_PER_WORD == 1 << NBYTE_PER_WORD_LOG)
 #define NBYTE_PER_WORD_MASK (NBYTE_PER_WORD - 1)
 #define GCATS2_TEST 1
 #define GCATS2_DEBUG 1
 #if (__WORDSIZE == 32)
 #define PTR_CHKSEG_SIZE 10
 #endif
 #if (__WORDSIZE == 64)
 #define PTR_CHKSEG_SIZE 9
 #endif
 #print "PTR_CHKSEG_SIZE = "; #print PTR_CHKSEG_SIZE; #print "\n"
 #define PTR_BOTSEG_SIZE 10
 #print "PTR_BOTSEG_SIZE = "; #print PTR_BOTSEG_SIZE; #print "\n"
 #define PTR_BOTCHKSEG_SIZE (PTR_BOTSEG_SIZE + PTR_CHKSEG_SIZE)
 #define PTR_TOPSEG_SIZE (NBIT_PER_WORD - PTR_BOTCHKSEG_SIZE - NBYTE_PER_WORD_LOG)
 #print "PTR_TOPSEG_SIZE = "; #print PTR_TOPSEG_SIZE; #print "\n"

 #define CHKSEG_TABLESIZE %(1 << PTR_CHKSEG_SIZE)
 #print "CHKSEG_TABLESIZE = "; #print CHKSEG_TABLESIZE; #print "\n"
 #define CHKSEG_TABLESIZE_MASK (CHKSEG_TABLESIZE - 1)

 #define BOTSEG_TABLESIZE %(1 << PTR_BOTSEG_SIZE)
 #print "BOTSEG_TABLESIZE = "; #print BOTSEG_TABLESIZE; #print "\n"
 #define BOTSEG_TABLESIZE_MASK (BOTSEG_TABLESIZE - 1)
 #if (__WORDSIZE == 32)
 #define TOPSEG_TABLESIZE (1 << PTR_TOPSEG_SIZE)
 #endif
 #if (__WORDSIZE == 64)
 #define TOPSEG_HASHTABLESIZE 4096
 #define TOPSEG_HASHTABLESIZE_LOG 12
 #define TOPSEG_HASHTABLESIZE_MASK (TOPSEG_HASHTABLESIZE - 1)
 #assert (TOPSEG_HASHTABLESIZE == 1 << TOPSEG_HASHTABLESIZE_LOG)
 #endif
 #define CHUNK_WORDSIZE_LOG PTR_CHKSEG_SIZE

 #define CHUNK_WORDSIZE %(1 << CHUNK_WORDSIZE_LOG)
 #define CHUNK_WORDSIZE_MASK (CHUNK_WORDSIZE - 1)
 #print "CHUNK_WORDSIZE = "; #print CHUNK_WORDSIZE; #print "\n"
 #define CHUNK_BYTESIZE_LOG (CHUNK_WORDSIZE_LOG + NBYTE_PER_WORD_LOG)
 #define CHUNK_BYTESIZE (1 << CHUNK_BYTESIZE_LOG)
 #define CHUNK_BYTESIZE_MASK (CHUNK_BYTESIZE - 1)
 #print "CHUNK_BYTESIZE = "; #print CHUNK_BYTESIZE; #print "\n"
 #assert (CHUNK_BYTESIZE == __PAGESIZE)
 #define MAX_CLICK_WORDSIZE_LOG CHUNK_WORDSIZE_LOG

 #define MAX_CLICK_WORDSIZE %(1 << MAX_CLICK_WORDSIZE_LOG)
 #assert (MAX_CLICK_WORDSIZE <= CHUNK_WORDSIZE)
 #print "MAX_CLICK_WORDSIZE = "; #print MAX_CLICK_WORDSIZE; #print "\n"
 #define FREEITMLST_ARRAYSIZE (MAX_CLICK_WORDSIZE_LOG + 1)
 #define MARKSTACK_PAGESIZE 4000
 #define NCHUNK_PER_MARKSTACKPAGE 64
 #define NMARKSTACKPAGE_OVERFLOW_EXTEND 2
 #define MARKSTACK_CUTOFF (CHUNK_WORDSIZE / 4)
 #define CHUNK_SWEEP_CUTOFF 0.50
 #assert (0.0 <= CHUNK_SWEEP_CUTOFF)
 #assert (CHUNK_SWEEP_CUTOFF <= 1.0)
 #define TOTWSZ_LIMIT_EXTEND_CUTOFF 0.75
 #assert (0.0 <= TOTWSZ_LIMIT_EXTEND_CUTOFF)
 #assert (TOTWSZ_LIMIT_EXTEND_CUTOFF <= 1.0)
 #define GLOBALRTS_PAGESIZE 100
 #assert (GLOBALRTS_PAGESIZE >= 1)

 #endif
