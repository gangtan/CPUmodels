./fuzzgen.native > fuzz.ascii
# This is move 0x0, eax, which will trigger segfault
# that's critical to cause the instructions after the
# move recent seg fault to print out
echo "a100000000" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
echo "9090909090" >> fuzz.ascii
# this is mov $0x1, %eax; int 0x80 which causes
# the program to exit
echo "b801000000" >> fuzz.ascii
echo "cd80" >> fuzz.ascii

echo "00000000" >> data.ascii
echo "00000000" >> data.ascii
echo "00000000" >> data.ascii
echo "00000000" >> data.ascii
echo "00000000" >> data.ascii
echo "00000000" >> data.ascii
echo "00000000" >> data.ascii

xxd -r -p fuzz.ascii > fuzz.hex
ld -m elf_i386 -r -b binary -o fuzz.eobj fuzz.hex
objcopy --rename-section .data=.text,contents,alloc,load,code fuzz.eobj
objcopy fuzz.eobj --globalize-symbol=_binary_fuzz_hex_start

xxd -r -p data.ascii > data.hex
ld -m elf_i386 -r -b binary -o data.eobj data.hex
objcopy --rename-section .data=.text,contents,alloc,load,code data.eobj
objcopy data.eobj --globalize-symbol=_binary_data_hex_start
gcc -m32 -o filter.out filter.c fuzz.eobj data.eobj

setarch i386 -R ./filter.out > fuzz.ascii.filtered
xxd -r -p fuzz.ascii.filtered > fuzz.hex
ld -m elf_i386 -r -b binary -o fuzz.eobj fuzz.hex
objcopy --rename-section .data=.text,contents,alloc,load,code fuzz.eobj
objcopy fuzz.eobj --globalize-symbol=_binary_fuzz_hex_start
gcc -m32 -o test.out test.c fuzz.eobj
