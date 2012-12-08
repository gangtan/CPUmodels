open X86Syntax
open PrettyPrinter
open Big
open Random

let choose_reg() = 
  coq_Z_to_register (of_int (Random.int 8))
  

let choose_word_int () = 
   power two (of_int (Random.int 32))
   
let choose_int8 () = 
   power two (of_int (Random.int 8))

let choose_int16 () = 
   power two (of_int (Random.int 16))
  
let choose_scale () = 
   coq_Z_to_scale (of_int (Random.int 4))

let choose_bool() = 
   Random.bool()

let choose_segment_reg() = 
	match (Random.int 6) with
	| 0 -> ES
	| 1 -> CS
	| 2 -> SS
	| 3 -> DS
	| 4 -> FS
	| _ -> GS

let choose_lock_or_rep() = 	
	match (Random.int 3) with 
	| 0 -> Coq_lock
	| 1 -> Coq_rep
	| _ -> Coq_repn

let choose_condition_type() =
	match (Random.int 15) with
	| 0 -> O_ct
	| 1 -> NO_ct
	| 2 -> B_ct
	| 3 -> NB_ct
	| 4 -> E_ct
	| 5 -> NE_ct
	| 6 -> BE_ct
	| 7 -> NBE_ct
	| 8 -> S_ct
	| 9 -> NS_ct
	| 10 -> P_ct
	| 11 -> NP_ct
	| 12 -> L_ct
	| 13 -> NL_ct
	| 14 -> LE_ct
	| _ -> NLE_ct
	
let choose_prefix () = 
	let lr_opt_c = choose_bool() in
        let sr_opt_c = choose_bool() in
        let op_c = choose_bool() in
        let addr_c = choose_bool() in

        let lock_rep = if lr_opt_c then Some (choose_lock_or_rep()) else None in
        let seg_override = if sr_opt_c then Some (choose_segment_reg()) else None in

        mkPrefix lock_rep seg_override op_c addr_c

let choose_addr() =
	let c_base = choose_bool() in
	let c_ind_scale_reg = choose_bool() in
	let displ = choose_word_int() in
	let base = if c_base then Some (choose_reg()) else None in
	let index = if c_ind_scale_reg then Some ((choose_scale()), (choose_reg())) else None in

	mkAddress displ base index

let choose_op() = 
  match (Random.int 4) with 
    0 -> let wint = choose_word_int () in Imm_op wint;
  | 1 -> let r = choose_reg () in Reg_op r;
  | 2 -> let addr = choose_addr() in Address_op addr;
  | _ -> let wint = choose_word_int () in Offset_op wint 

let choose_ADC () = 
  let b = choose_bool()in
  let op1 = choose_op() in
  let op2 = choose_op() in
  ADC (b, op1, op2)

let choose_ADD ()= 
  let b = choose_bool() in
  let op1 = choose_op() in
  let op2 = choose_op() in
  ADD (b, op1, op2)
  ;;

let choose_AND () = 
  let b = choose_bool() in
  let op1 = choose_op () in
  let op2 = choose_op() in
  AND (b, op1, op2)
  ;;

let choose_ARPL () = 
  let op1 = choose_op () in
  let op2 = choose_op () in
  ARPL (op1, op2)
  ;;  

let choose_BOUND () = 
  let op1 = choose_op () in
  let op2 = choose_op () in
  BOUND (op1, op2)
  ;;

let choose_BSF () = 
  let op1 = choose_op () in
  let op2 = choose_op () in
  BSF (op1, op2)
  ;;

let choose_BSR () = 
  let op1 = choose_op () in
  let op2 = choose_op () in
  BSR (op1, op2)
  ;;

let choose_BSWAP () = 
  let reg = choose_reg () in
  BSWAP reg
  ;;

let choose_BT () = 
  let op1 = choose_op () in
  let op2 = choose_op () in
  BT (op1, op2)
  ;;

let choose_BTC () = 
  let op1 = choose_op () in
  let op2 = choose_op () in
  BTC (op1, op2)
  ;;

let choose_BTR () = 
  let op1 = choose_op () in
  let op2 = choose_op () in
  BTR (op1, op2)
  ;;

let choose_BTS () = 
  let op1 = choose_op () in
  let op2 = choose_op () in
  BTS (op1, op2)
  ;;

let choose_CALL () = 
	let near_c = choose_bool() in
	let abs_c = choose_bool() in
	let opt_c = choose_bool() in
  	let selector = if opt_c then Some (choose_int16 ()) else None in
	let op1 = choose_op() in
  	CALL (near_c, abs_c, op1, selector)
 	;;

let choose_CMOVcc () = 
	let ct = choose_condition_type () in
	let op1 = choose_op () in
	let op2 = choose_op () in
	CMOVcc (ct, op1, op2) 
	;;

let choose_CMP () = 
	let wc = choose_bool() in
	let op1 = choose_op () in
	let op2 = choose_op () in
	CMP (wc, op1, op2)
	;;

let choose_CMPS() = 
	CMPS (choose_bool())
	;;

let choose_CMPXCHG () = 
	let wc = choose_bool() in
	let op1 = choose_op () in
	let op2 = choose_op () in
	CMPXCHG (wc, op1, op2)
	;;

let choose_DEC ()= 
	let wc = choose_bool() in
	let op1 = choose_op () in
	DEC (wc, op1)
	;;

let choose_DIV ()= 
	let wc = choose_bool() in
	let op1 = choose_op () in
	DIV (wc, op1)
	;;

let choose_IDIV () = 
	let wc = choose_bool() in
	let op1 = choose_op () in
	IDIV (wc, op1)
	;;

let choose_IMUL() = 
	let wc = choose_bool() in
	let opt_c = choose_bool() in
	let intopt_c = choose_bool() in
	let op1 = choose_op () in
	let op2 = if opt_c then (Some (choose_op())) else None in
	let i32 = if intopt_c then (Some (choose_word_int())) else None in
	IMUL (wc, op1, op2, i32)
	;;

let choose_IN () = 
	let wc = choose_bool() in
	let opt_c = choose_bool() in
	let port_num = if opt_c then (Some (choose_int8())) else None in
	IN (wc, port_num)
	;;

let choose_INC ()= 
	let wc = choose_bool() in
	let op1 = choose_op () in
	INC (wc, op1)
	;;

let choose_INS () = 
	INS (choose_bool())
	;;

let choose_INTn() = 
	let it = choose_word_int() in
	INTn it
	;;

let choose_INVLPG () = 
	let op1 = choose_op () in
	INVLPG op1
	;;

let choose_Jcc ()= 
	let ct = choose_condition_type () in
	let disp = choose_int8 () in
	Jcc (ct, disp)
	;;

let choose_JCXZ () = 
	let b = choose_int8() in
	JCXZ b
	;;

let choose_JMP () = 
	let near_c = choose_bool() in
	let abs_c = choose_bool() in
	let opt_c = choose_bool() in
	let op1 = choose_op() in
	let sel = if opt_c then (Some (choose_int16 ())) else None in
	JMP (near_c, abs_c, op1, sel)
	;;
 
(** returns a random gp instruction  **)
let choose_gp_instr()  = 
 (* print_string "c:\n";
  print_int c; *)
   match (Random.int 50) with 
      0 -> choose_ADC(); 
    | 1 -> choose_ADD (); 
    | 2 -> choose_AND (); 
    | 3 -> AAA
    | 4 -> AAD
    | 5 -> AAM
    | 6 -> AAS
    | 7 -> choose_ARPL ();
    | 8 -> choose_BOUND ();
    | 9 -> choose_BSF ();
    | 10 -> choose_BSR ();
    | 11 -> choose_BSWAP ();
    | 12 -> choose_BT ();
    | 13 -> choose_BTC ();
    | 14 -> choose_BTR ();
    | 15 -> choose_BTS ();
    | 16 -> choose_CALL ()
    | 17 -> CDQ
    | 18 -> CLC
    | 19 -> CLD
    | 20 -> CLI
    | 21 -> CLTS
    | 22 -> CMC
    | 23 -> choose_CMOVcc ()
    | 24 -> choose_CMP ()
    | 25 -> choose_CMPS ()
    | 26 -> choose_CMPXCHG ()
    | 27 -> CWDE
    | 28 -> DAA
    | 29 -> DAS
    | 30 -> choose_DEC ()
    | 31 -> choose_DIV ()
    | 32 -> CPUID
    | 33 -> CWDE
    | 34 -> HLT
    | 35 -> choose_IDIV ()
    | 36 -> choose_IMUL ()
    | 37 -> choose_IN () 
    | 38 -> choose_INC ()
    | 39 -> choose_INS ()
    | 40 -> choose_INTn ()
    | 41 -> INT
    | 42 -> INTO
    | 43 -> INVD
    | 44 -> choose_INVLPG ()
    | 45 -> IRET
    | 46 -> choose_Jcc ()
    | 47 -> choose_JCXZ ()
    | 48 -> choose_JMP ()
    | 49 -> LAHF 
    | _ -> choose_ARPL ()  (*dummy *)
    
let rec fuzz_gp n = 
  match n with 
    | 0 -> ()
    | x ->   
     let prefix = choose_prefix () in
     let instr = choose_gp_instr () in 
   (*  pp_prefix_instr (prefix, instr);  *)
     pp_instr (prefix, instr); 
     print_string "\n";
     fuzz_gp (x - 1) 
  ;;

Random.self_init();;

let main () = 
  print_string("running syntaxfuzzer:\n");
  
  fuzz_gp 500;;

main();;
