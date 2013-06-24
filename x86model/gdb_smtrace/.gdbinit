set logging on
set confirm off
set height 0
set print pretty on
set output-radix 0x10
set input-radix 0x10
set disassembly-flavor intel

break main
run

define printf_fp_regs
	printf "st0: %08x\n", $st0
	printf "st1: %08x\n", $st1
	printf "st2: %08x\n", $st2
	printf "st3: %08x\n", $st3
	printf "st4: %08x\n", $st4
	printf "st5: %08x\n", $st5
	printf "st6: %08x\n", $st6
	printf "st7: %08x\n", $st7
end

define smtrace
 step
 set $count = 0
 while 1
  printf "\n"
  printf "***iteration #: %i \n", $count
  printf "\n"
  printf_fp_regs
  info registers
 # info all-registers
  x /i $pc
  set $count++
  stepi
 end
end

smtrace
printf "finished running smtrace"
quit