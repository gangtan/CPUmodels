#!/bin/bash

if [ $# != 2 ] 
then
    echo Usage: ./run.sh my_file.c end_symbol
else
    echo Compiling $1 
    rm test
    gcc -static $1 -o test
    if [ -e test ]
    then
	echo Instrumentation
	setarch i386 -R $PIN_PATH/pin -injection child -t memlist.so -e "$2" -- ./test
	setarch i386 -R $PIN_PATH/pin -injection child -t gntrace.so -e "$2" -- ./test
    else
	echo Compilation of $1 failed	
    fi
fi
