/* 

   This generates a dump of the memory/register values as 
   a program executes. Replaces an earlier less-portable pthread tool. 

   Depends on the Pin instrumentation/dynamic analysis tool developed by Intel. 
 
*/

#include <fstream>
#include <iostream>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "pin.H"
#include "tracer.h"

KNOB<string> KnobStartSymbol(KNOB_MODE_WRITEONCE, "pintool",
			     "s", "main", "specify function to start tracing from");

KNOB<string> KnobEndSymbol(KNOB_MODE_WRITEONCE, "pintool",
			   "e", "", "specify function to stop tracing from");

KNOB<string> KnobMaxInstrs(KNOB_MODE_WRITEONCE, "pintool",
			   "m", "5000", "specify max number of instructions to trace");

FILE * memtrace;
FILE * regtrace;
FILE * flagtrace;
int flag = 0;
int found = 0;
int lastinssyscall = 0;
int dumpnum = 0;
// Used to count the number of instructions we've traced.
unsigned int counter = 0;
unsigned int max_instrs = 0;
unsigned int image_start_size = 0;
unsigned int image_end_size = 0;

VOID dumpmem(int last) {
  char filename[80];
  sprintf(filename, "mem%d.txt", dumpnum);
  memtrace = fopen(filename, "w");
  FILE * memaddrs = fopen("memaddrs.txt", "r");
  unsigned int *addr = 0;
  unsigned int tmp = 0;
  tmp = 0;
  while( fscanf(memaddrs, "%08x\n", (unsigned int *) &addr) == 1) {
    PIN_SafeCopy(&tmp, addr, 1);
    fprintf(memtrace, "%08x %02x\n", (unsigned int) (addr), tmp);
  }
  fclose(memaddrs);
  fclose(memtrace);
  if(dumpnum > 0) {
    fprintf(regtrace, "END 0");
    fclose(regtrace);
  }
  if(!last) {
    sprintf(filename, "regs%d.txt", dumpnum);
    regtrace = fopen(filename, "w");
    dumpnum++;
  }
}


// This function runs every time an instruction is executed.  If the flag is
// turned on, it dumps out the memory for that instruction as well as the
// register values / eflags prior to executing the instruction. 

VOID dumpins(char * ip, unsigned int sysflag, USIZE size, ADDRINT* EAX, ADDRINT* ECX, ADDRINT* EDX, ADDRINT* EBX,
	     ADDRINT* ESP, ADDRINT* EBP, ADDRINT* ESI, ADDRINT* EDI, ADDRINT *FS,
	     ADDRINT* GS, UINT32 eflags)
{

  if(flag >= 1 && counter < max_instrs) {
    if(lastinssyscall) {
      /* the last thing we did was a syscall. Therefore we must do a memory dump
	 and start up a new register file. */
      dumpmem(0);
      lastinssyscall = 0;
    }
    if(sysflag) {
      printf("Encountered syscall at %08x\n", (unsigned int) ip);
      lastinssyscall = 1;  
    }
    fprintf(regtrace, "FS %08x\n", *FS);
    fprintf(regtrace, "GS %08x\n", *GS);
    fprintf(regtrace, "EAX %08x\n", *EAX);
    fprintf(regtrace, "ECX %08x\n", *ECX);
    fprintf(regtrace, "EDX %08x\n", *EDX);
    fprintf(regtrace, "EBX %08x\n", *EBX);
    fprintf(regtrace, "ESP %08x\n", *ESP);
    fprintf(regtrace, "EBP %08x\n", *EBP);
    fprintf(regtrace, "ESI %08x\n", *ESI);
    fprintf(regtrace, "EDI %08x\n", *EDI);
    fprintf(regtrace, "EIP %08x\n\n", (unsigned int) ip);
    //fprintf(flagtrace, "%08x\n\n", (unsigned int) eflags);
    counter++;
  }

  if(flag == 2 || !(counter < max_instrs)) {
     printf("Done recording.\n");
     dumpmem(1);
     PIN_ExitApplication(0);
  }
}
VOID startrecord(ADDRINT* ESP) {
  flag = 1;
  // Dump out all of the memory addresses that we identified as relevant in the previous pass
  dumpmem(0);
}

VOID endrecord() {
  flag = 2;
}

VOID ins_instrument(INS ins, VOID *v)
{
  unsigned int sysflag = INS_IsSyscall(ins) ? 1 : 0;
  INS_InsertCall(ins, 
		 IPOINT_BEFORE, 
		 (AFUNPTR)dumpins,
		 IARG_INST_PTR, 
		 IARG_UINT32,
		 sysflag,
		 IARG_UINT32, 
		 INS_Size(ins), 
		 IARG_REG_REFERENCE, REG_EAX,
		 IARG_REG_REFERENCE, REG_ECX,
		 IARG_REG_REFERENCE, REG_EDX,
		 IARG_REG_REFERENCE, REG_EBX,
		 IARG_REG_REFERENCE, REG_ESP,
		 IARG_REG_REFERENCE, REG_EBP,
		 IARG_REG_REFERENCE, REG_ESI,
		 IARG_REG_REFERENCE, REG_EDI,
		 IARG_REG_REFERENCE, REG_SEG_FS_BASE,
		 IARG_REG_REFERENCE, REG_SEG_GS_BASE,
		 IARG_REG_VALUE, REG_EFLAGS,
		 IARG_END);
}    

void init_start_stop(IMG img, void * b) {
  if(found) return;
  unsigned long start_addr = find_symbol(IMG_Name(img).c_str(), "main");
  unsigned long end_addr = find_symbol(IMG_Name(img).c_str(), KnobEndSymbol.Value().c_str());
  image_start_size = IMG_LowAddress(img);
  image_end_size   = IMG_HighAddress(img);
  RTN start = RTN_FindByName(img, "main");
  if(!RTN_Valid(start) && (image_start_size <= start_addr) && (start_addr <= image_end_size)) {
    start = RTN_CreateAt(start_addr, "main");
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

  /*flagtrace = fopen("flags0.txt", "w"); */

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

