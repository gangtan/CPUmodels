#include <string.h>
#include <stdlib.h>

uint8_t *valid;
uint8_t *target;
  
Bool match(DFA *A, uint8_t *code, uint *pos, uint size) {

  uint8_t state = A->start;
  uint off = 0;

  while (*pos + off < size) {

    state = A->table[state][code[*pos + off]];
    off++;

    if (A->rejects[state]) break;
    
    if (A->accepts[state]) { 
      *pos += off;
      return TRUE;
    }
    
  }    
  
  return FALSE;  
} 

int compute_rel(uint8_t *code, uint nbytes) {
  uint i; 
  uint32_t acc = 0;

  for (i = 0; i < nbytes; ++i) 
    acc += (code[i] << (8 * i));
  
  return acc;
}

Bool extract(uint8_t *code, uint start_pos, uint new_pos) {
  
  uint8_t b1, b2;
  Bool ok = FALSE;

  b1 = code[start_pos];
  if (b1 != 0x0F) {
    if (((0x70 <= b1) && (b1 <= 0x7F)) || (b1 == 0xE3) || (b1 == 0xEB)) {
      target[new_pos+ (int8_t) compute_rel(&code[start_pos+1],1)] = 1;
      ok = TRUE;
    }
    if ((b1 == 0xE9) || (b1 == 0xE8)) {
      if (compute_rel(&code[start_pos+1],4) < 0) {
	if ((new_pos + compute_rel(&code[start_pos+1],4)) % 32 == 0) {
	  ok = TRUE;
	}
      }
      else{
	target[new_pos+ compute_rel(&code[start_pos+1],4)] = 1;
	ok = TRUE;
      }
    }  
  }
  else {
    b2 = code[start_pos+1];
    
    if (((0x80 <= b2) && (b2 <= 0x8F))) {
      target[new_pos+ compute_rel(&code[start_pos+2],4)] = 1;
      ok = TRUE;
    }
  }
  
  return (ok?1:0);
}

Bool verifier(DFA *NonControlFlow, 
	     DFA *DirectJump, 
	     DFA *MaskedJump, 
	     uint8_t *code, uint size) {

  uint pos = 0, i, saved_pos;
  Bool b = TRUE;

  valid = (uint8_t *) calloc(size * sizeof(uint8_t),sizeof(uint8_t));
  target = (uint8_t *) calloc(size * sizeof(uint8_t),sizeof(uint8_t));

  while (pos < size) {
    valid[pos] = TRUE;
    saved_pos = pos;

    if (match(MaskedJump,code,&pos,size)) continue;
    
    if (match(NonControlFlow,code,&pos,size)) continue;
   
    if (match(DirectJump,code,&pos,size)) 
      if (extract(code,saved_pos,pos)) continue; 
    
    return FALSE;
  }

  for (i = 0; i < size; ++i) 
    b = b && 
      ( !(target[i]) || valid[i] ) && 
      ( i & 0x1F || valid[i] ); 
		   
  return b;
}


      
  
