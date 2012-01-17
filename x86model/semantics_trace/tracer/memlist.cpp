/* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*/


/* 

   This generates a list of memory addresses accessed by the binary. This file is
   used in later instrumentation passes.
   
   Depends on the Pin instrumentation/dynamic analysis tool developed by Intel. 
   See the examples in the manual, especially pinatrace for information about
   accessing memory operands with Pin.
 
*/

#include <fstream>
#include <iostream>
#include <stdlib.h>
#include <string.h>
#include "pin.H"
#include "tracer.h"


/* Some options. KNOBs are Pin's way of setting up config info.
   -s switch specifies the starting function to trace from
   -e is the symbol name to stop tracing at
   -m is the maximum number of instructions to trace
*/
 
KNOB<string> KnobStartSymbol(KNOB_MODE_WRITEONCE, "pintool",
			     "s", "main", "specify function to start tracing from");

KNOB<string> KnobEndSymbol(KNOB_MODE_WRITEONCE, "pintool",
			   "e", "", "specify function to stop tracing from");

KNOB<string> KnobMaxInstrs(KNOB_MODE_WRITEONCE, "pintool",
			   "m", "5000", "specify max number of instructions to trace");


FILE * memtrace;
// Used to count the number of instructions we've traced.
unsigned int counter = 0;
unsigned int max_instrs = 0;
unsigned int image_start_size = 0;
unsigned int image_end_size = 0;

// A flag for determining if we're in record mode or not 
unsigned int flag = 0;
unsigned int found = 0;

// This function runs every time an instruction is executed.  If the flag is
// turned on, it dumps out the memory addresses for that instruction

VOID dumpins(char * ip, USIZE size)
{
  if(flag && counter < max_instrs) {
    for(unsigned int i = 0; i < size; i++){
      fprintf(memtrace, "%08x\n", (unsigned int) (ip+i));
    }
    counter++;
  }
}

VOID readmem (char * ip, VOID * addrvoid, USIZE size) {
  // An address in memory was read. 
  // We should record this as an address worth watching.
  char * addr = (char *) addrvoid;
  if (counter < max_instrs) {
    for(unsigned int i = 0; i < size; i++) {	
      fprintf(memtrace, "%08x\n", (unsigned int) (addr+i));
    }
  }
}

VOID startrecord(ADDRINT* ESP) {
  flag = 1;
}

VOID endrecord() {
  flag = 0;
  PIN_ExitApplication(0);
}

VOID ins_instrument(INS ins, VOID *v)
{
  INS_InsertCall(ins, 
		 IPOINT_BEFORE, 
		 (AFUNPTR)dumpins,
		 IARG_INST_PTR, 
		 IARG_UINT32, 
		 INS_Size(ins), 
		 IARG_END);
  UINT32 memop_count = INS_MemoryOperandCount(ins);
  UINT32 i = 0;
  for(i = 0; i < memop_count; i++) {
    if(INS_MemoryOperandIsRead(ins, i)) {
      INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) readmem, IARG_INST_PTR,
		     IARG_MEMORYOP_EA, i,
		     IARG_UINT32, INS_MemoryOperandSize(ins, i), IARG_END);
    }
  }
}    

void init_start_stop(IMG img, void * b) {
  // We attempt to find the desired symbol names in each of the images.
  // We do not use Pin's default tool for doing this because it working in some
  // cases. Instead we write a custom function that calls nm to extract this info.
  // see tracer.h
 
  if(found) return;
  unsigned long start_addr = find_symbol(IMG_Name(img).c_str(), "main");
  unsigned long end_addr = find_symbol(IMG_Name(img).c_str(), KnobEndSymbol.Value().c_str());
  image_start_size = IMG_LowAddress(img);
  image_end_size   = IMG_HighAddress(img);
  RTN start = RTN_FindByName(img, "main");
  if(!RTN_Valid(start) && (image_start_size <= start_addr) && (start_addr <= image_end_size)) {
    start = RTN_CreateAt(start_addr, "end");
  }

  RTN end = RTN_FindByName(img, KnobEndSymbol.Value().c_str());
  if(!RTN_Valid(end) && (image_start_size <= end_addr) && (end_addr <= image_end_size)) {
    end = RTN_CreateAt(end_addr, "end");
  }

  if(RTN_Valid(start) && RTN_Valid(end)) {
    RTN_Open(start);
    RTN_InsertCall(start, IPOINT_BEFORE, (AFUNPTR)startrecord, IARG_REG_REFERENCE, REG_ESP, IARG_END);
    RTN_Close(start);

    RTN_Open(end);
    RTN_InsertCall(end, IPOINT_BEFORE, (AFUNPTR)endrecord, IARG_END);
    RTN_Close(end);
    printf("Found end/start\n");
    found = 1;
  }
  else {
    printf("Couldn't find either end/start in this image.\n");
  }
}
	


int main(int argc, char * argv[])
{
  if (PIN_Init(argc, argv)) return -1;

  if(strcmp(KnobEndSymbol.Value().c_str(), "") == 0) {
    cerr << "Need to specify symbol to stop tracing at using the -e switch";
    cerr << endl;
    return -1;
  }

  max_instrs = atoi(KnobMaxInstrs.Value().c_str());
  PIN_InitSymbols();

  memtrace = fopen("memaddrs.txt", "w");

  // This adds instrumentation to the functions "main" and the stop symbol
  // specified by the -e switch. 

  IMG_AddInstrumentFunction(init_start_stop, 0);

  // This instruments every instruction with a call to a function that either
  // dumps/does not dump mem/regs/eflags based on the flag switched when we
  // reach the start/end symbols.

  INS_AddInstrumentFunction(ins_instrument, 0);    

  PIN_StartProgram();
    
  return 0;
}

