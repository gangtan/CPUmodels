/* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

unsigned long find_symbol(const char *, const char *);

/* 
   This takes in the name of an executable and a symbol name,
   and finds the address of that symbol by calling "nm <proc>"
  
   For some reason PIN wasn't finding some symbols on it's own.
   I suspect that this is not the most robust approach. For example
   this won't let you find the address of symbols that are dynamically
   loaded, but we don't need that for our testing purposes. 
*/

unsigned long find_symbol(const char *proc, const char *symname) {
  char nmcall[256];
  char output[512];
  char tempname[256];
  strcpy(nmcall, "nm ");
  strcat(nmcall, proc);
  FILE * nmout = popen(nmcall, "r");

  while(fgets(output, 512, nmout) != 0) {
    unsigned long loc = 0;
    // This sscanf formatting string extracts the location and symbol name from a line of
    // nm output

    if(sscanf(output, "%lx %*[^ \n] %[^ \n]", &loc, tempname) == 2) {
        if(!strcmp(symname, tempname)) {
		return loc;
	}
    }
  }
  return 0;
}
