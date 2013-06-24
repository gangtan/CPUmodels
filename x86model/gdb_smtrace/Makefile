
smtrace:
	gcc -g main.c -o main
	rm gdb.txt
	rm instrs.txt
	cp gdb_init .gdbinit
	objdump -D main > instrs.txt
	gdb --eval-command=run --eval-command=quit --args main