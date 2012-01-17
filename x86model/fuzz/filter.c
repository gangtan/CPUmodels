/* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*/


/* 
  This file contains C code that, when linked with a binary produced from
  the output of fuzzgen.ml, will run the instructions outputted by fuzzgen.ml
  and attempt to strip out any instructions that cause a SIGSEGV. 

  What happens is that the initial output of fuzzgen.ml has been padded with
  NOPS in between instructions. This C file registers a signal handler for 
  SIGSEGV before jumping to the output of fuzzgen. The signal handler 
  bumps the EIP of the context in which the segfault happened by 15, which
  will push us past the instruction that caused the segfault and into the 
  NOPs. Because instruction lengths vary, the place we end up in the NOPs will
  vary, but that is ok, because they will just act like a sled. 

  Before doing this, the signal handler prints out all the instructions from
  the last time we did this up until the current SEGFault causing-offender.

  The result is that we output a file which contains only the instructions
  that did not trigger a segfault. The NOPs are also filtered out. This 
  output is then ready to be converted to a binary and linked with another 
  test driver. 

  Granted, it is possible for an instruction that did not trigger a segfault
  here to trigger a segfault when loaded with different code and in a different
  position, but in practice this actually tends to work pretty well. Also, the stuff
  we do in the handler is NOT allowed in good C code (ie: doing file io). But hey,
  we're also about to transfer control to a randomly generated binary, so we've
  already thrown caution to the wind. Also, this is all highly Linux specific 
  as best I can tell.
*/

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
/* If you include this #define statement you get nice macros/names for
 * modifying ucontext_t data structure, which  we will be doing here 
*/
#define __USE_GNU
#include <signal.h>
#include <ucontext.h>
#include <dlfcn.h>
#include <fcntl.h>

struct sigaction action;

/* These are symbols that will be added when we link against the 
   binary created from the fuzzgen.ml output 
   
   _binary_fuzz_hex_start is the symbol that marks the beginning
   of the fuzz generated code. We will call it as a function in order
   to jump to it.

   _binary_data_hex_start is an array that indicates which of the generated
   bytes from fuzzgen.ml output are just NOPs, we will filter these out 
   so that we don't waste our time simulating NOPS.
*/
void _binary_fuzz_hex_start();

extern char _binary_data_hex_start[];

// This will keep track of the last EIP that we printed a dump from
unsigned int * last_good = _binary_fuzz_hex_start;

void test(int sig, siginfo_t * info, ucontext_t * context) 
{
  unsigned int i = 0;
  unsigned int tmp = 0;

  /* Loop through reading out all of the byte code for the instructions in between
     the last time we did such a dump and the current offending instruction */
  for(i = 0; i < (context->uc_mcontext.gregs[REG_EIP] - (unsigned int) last_good); i++) {	
    
    // Only print it out if it isn't a nop (ie _binary_data_hex_start for this EIP value isn't 0
    if(_binary_data_hex_start[(unsigned int) last_good + i - (unsigned int)_binary_fuzz_hex_start]) {
    	tmp = *((unsigned int *) ( (unsigned int) last_good + i));
    	tmp &= 0x000000FF;
    	printf("%02x\n", tmp);
    } 

  }

  // Always good to flush this. 
  fflush(stdout);

  // Bump EIP by 15 so that when we return we will have moved past the 
  // offending instruction
  context->uc_mcontext.gregs[REG_EIP] += 15;
  last_good = context->uc_mcontext.gregs[REG_EIP];  
}


int main()
{
  // Register the signal handler. We're using sigaction instead of the
  // simpler sighandler stuff because we need access to context 
  action.sa_flags = SA_SIGINFO;
  action.sa_sigaction = test;
  sigaction(SIGSEGV, &action, NULL);

  // Transfer control to the fuzz generated code
  _binary_fuzz_hex_start();	
}
