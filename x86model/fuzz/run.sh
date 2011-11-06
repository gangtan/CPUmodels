#!/bin/bash

if [ $# != 2 ] 
then
    echo Usage: ./run.sh executable end_symbol
else
    if [ -e $1 ]
    then
	echo Instrumentation
	setarch i386 -R $PIN_PATH/pin -injection child -t ../semantics_trace/memlist.so -e "$2" -- ./$1
	sort memaddrs.txt > tmp0
	uniq tmp0 > memaddrs.txt
	setarch i386 -R $PIN_PATH/pin -injection child -t ../semantics_trace/gntrace.so -e "$2" -- ./$1
    else
	echo $1 does not exist.
    fi
fi
