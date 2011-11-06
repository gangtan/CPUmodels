MIPS Model:

A model of ~50 instructions for a modern 32bit MIPS machine, with no coprocessor or floating point support.
However, this model does take branch delays into account.

Most of this was taken directly from the x86model directory. 
Changes were made in Decode.v, X86/MIPSSemantics.v, and X86/MIPSSyntax.v
to adapt it to the MIPS processor.

The extracted/ directory contains a MIPS testing framework, which currently
allows for assembly code to be assembled and run on a blank machine,
Harvard Architecture style, so the code is not actually in main memory.
The test output can be compared against what MARS or SPIM would do.

To do a test do the following:
run "make" in the MIPSModel/ directory to compile the coq
run "make extract" in the MIPSModel/extracted/ directory to extract ml
run "make compile" in the MIPSModel/extracted/ directory to compile ml
run "make" in MIPSModel/extracted/tests directory to assemble MARS MIPS asm code in "test.asm" into hex values
run "make run" in MIPSModel/extracted to run the test

--EG
