set logging off
set confirm off
set height 0
set output-radix 0x10
set input-radix 0x10

set print pretty on
set print address off
set print demangle off
set print thread-events off
set print symbol-filename off
set print static-members off
set print pascal_static-members off
set print union off
set print entry-values no

break main
run

define println
	printf "\n"
end

define printf_fp_regs
	set logging on
	printf "st0: %08x\n", $st0
	printf "st1: %08x\n", $st1
	printf "st2: %08x\n", $st2
	printf "st3: %08x\n", $st3
	printf "st4: %08x\n", $st4
	printf "st5: %08x\n", $st5
	printf "st6: %08x\n", $st6
	printf "st7: %08x\n", $st7

	printf "fctrl: %08x\n", $fctrl
	printf "fstat: %08x\n", $fstat
	printf "ftag:  %08x\n", $ftag
	printf "fiseg: %08x\n", $fiseg
	printf "fioff: %08x\n", $fioff
	printf "foseg: %08x\n", $foseg
	printf "fooff: %08x\n", $fooff
	printf "fop:   %08x\n", $fop
	println

	set logging off
end

define print_gp_regs
	set logging on
	info registers
	println
	set logging off
end

define print_all_info
	set logging on
	info all-registers
	set logging off
end

define print_address
	set logging on
	println
	x/i $pc
	set logging off
end

define smtrace
 step
 set $count = 0
 while 1
  set logging on
  println
  printf "***iteration #: %i \n", $count
  println
  set logging off
  print_gp_regs
  printf_fp_regs
 # print_all_info
  print_address
  set $count++
  nexti
 end
end

smtrace
printf "finished running smtrace"
quit
