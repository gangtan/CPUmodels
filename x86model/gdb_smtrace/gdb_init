set logging off
set confirm off
set height 0
set output-radix 0x10
set input-radix 0x10

set print pretty on
set print address on
set print demangle off
set print thread-events off
set print symbol-filename off
set print static-members off
set print pascal_static-members off
set print union off
set print entry-values no
set disassembly-flavor intel

#break main
#break __libc_start_main
#break exit
start

define println
	printf "\n"
end

define printf_fp_regs
	set logging on

#this doesn't work as $st0..$st7 store
#the actual floating-point values, and
#printf truncates them to ints
#	printf "st0:   %08x\n", $st0
#	printf "st1:   %08x\n", $st1
#	printf "st2:   %08x\n", $st2
#	printf "st3:   %08x\n", $st3
#	printf "st4:   %08x\n", $st4
#	printf "st5:   %08x\n", $st5
#	printf "st6:   %08x\n", $st6
#	printf "st7:   %08x\n", $st7

#this trick doesn't work either because
#convenience variable addresses can't be accessed.
#	if $st7
#		set $tmpp = * (int *)(&$st7)
#	end

#for now, this will have to do
	info registers $st0
	info registers $st1
	info registers $st2
	info registers $st3
	info registers $st4
	info registers $st5
	info registers $st6
	info registers $st7


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
	#info registers
	println

	printf "eax:    %08x\n", $eax
	printf "ecx:    %08x\n", $ecx
	printf "edx:    %08x\n", $edx
	printf "ebx:    %08x\n", $ebx
	printf "esp:    %08x\n", $esp
	printf "ebp:    %08x\n", $ebp
	printf "esi:    %08x\n", $esi
	printf "edi:    %08x\n", $edi
	printf "eip:    %08x\n", $eip
	printf "eflags: %08x\n", $eflags
	printf "cs:     %08x\n", $cs
	printf "ss:     %08x\n", $ss
	printf "ds:     %08x\n", $ds
	printf "es:     %08x\n", $es
	printf "fs:     %08x\n", $fs
	printf "gs:     %08x\n", $gs
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

	#Output 4 words of data memory going back from the stack pointer
	x/24xw $sp

#	x/20w main
#	x/4w $pc
#	what (0x843e58955)
#	print $pc
#	where
#	x/i $pc
#	mem 804a000 0
#	x/5i 8049000
#	printf "current memory addr: %08x\n", $pc
#	printf "disassembly:\n"
#	disassemble /r  
#	x/100xw $pc
#	println
#	info mem
#The command below (info proc mappings) is promising to get the starting and ending address
#locations
#	info proc mappings
#	info proc
#	info files
#	maintenance info sections
	set logging off
end

define smtrace
 step
 set $count = 0

 #hacky, but so far the only way I can detect when program ends
 #this is the address of libc_start_main
 while ($pc != 400524d3)
  set logging on
  output $ps
  println
  printf "***iteration #: %i \n", $count
  println
  set logging off
  print_gp_regs
  printf_fp_regs
#  print_all_info
# print_address
  set $count++
  nexti
#  stepi
 end
end

smtrace
continue

printf "finished running smtrace\n"

quit
