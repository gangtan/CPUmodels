
all: gntrace.so memlist.so


gntrace.so: gntrace.cpp tracer.h
	g++ -m32 -c -Wall -Werror -Wno-unknown-pragmas  -O3 -fomit-frame-pointer -DBIGARRAY_MULTIPLIER=1 -DUSING_XED  -fno-strict-aliasing -I$(PIN_PATH)/extras/xed2-ia32/include -I$(PIN_PATH)/extras/components/include -I$(PIN_PATH)/source/include -I$(PIN_PATH)/source/include/gen -fno-stack-protector -DTARGET_IA32 -DHOST_IA32 -DTARGET_LINUX -O3 -fomit-frame-pointer -o gntrace.o gntrace.cpp 
	g++  -m32 -Wl,--hash-style=sysv -shared -Wl,-Bsymbolic -Wl,--version-script=$(PIN_PATH)/source/include/pintool.ver -L$(PIN_PATH)/extras/xed2-ia32/lib -L$(PIN_PATH)/ia32/lib -L$(PIN_PATH)/ia32/lib-ext  -o gntrace.so gntrace.o -L$(PIN_PATH)/extras/xed2-ia32/lib -L$(PIN_PATH)/ia32/lib -L$(PIN_PATH)/ia32/lib-ext -lpin  -lxed -ldwarf -lelf -ldl  

memlist.so: memlist.cpp tracer.h
	g++ -m32 -c -Wall -Werror -Wno-unknown-pragmas  -O3 -fomit-frame-pointer -DBIGARRAY_MULTIPLIER=1 -DUSING_XED  -fno-strict-aliasing -I$(PIN_PATH)/extras/xed2-ia32/include -I$(PIN_PATH)/extras/components/include -I$(PIN_PATH)/source/include -I$(PIN_PATH)/source/include/gen -fno-stack-protector -DTARGET_IA32 -DHOST_IA32 -DTARGET_LINUX -O3 -fomit-frame-pointer -o memlist.o memlist.cpp
	g++  -m32 -Wl,--hash-style=sysv -shared -Wl,-Bsymbolic -Wl,--version-script=$(PIN_PATH)/source/include/pintool.ver -L$(PIN_PATH)/extras/xed2-ia32/lib -L$(PIN_PATH)/ia32/lib -L$(PIN_PATH)/ia32/lib-ext  -o memlist.so memlist.o -L$(PIN_PATH)/extras/xed2-ia32/lib -L$(PIN_PATH)/ia32/lib -L$(PIN_PATH)/ia32/lib-ext -lpin  -lxed -ldwarf -lelf -ldl  
