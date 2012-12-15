open BinInt
open Bits
open Maps
open Monad
open Peano_dec

type __ = Obj.t

(** val size1 : Big.big_int **)

let size1 =
  Big.zero

(** val size2 : Big.big_int **)

let size2 =
  Big.succ Big.zero

(** val size3 : Big.big_int **)

let size3 =
  Big.succ (Big.succ Big.zero)

(** val size4 : Big.big_int **)

let size4 =
  Big.succ (Big.succ (Big.succ Big.zero))

(** val size8 : Big.big_int **)

let size8 =
  Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero))))))

(** val size16 : Big.big_int **)

let size16 =
  Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ Big.zero))))))))))))))

(** val size32 : Big.big_int **)

let size32 =
  Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ Big.zero))))))))))))))))))))))))))))))

(** val size64 : Big.big_int **)

let size64 =
  Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val size80 : Big.big_int **)

let size80 =
  Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ
    Big.zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type int = Word.int

module type MACHINE_SIG = 
 sig 
  type location 
  
  val size_addr : Big.big_int
  
  type mach_state 
  
  val get_location : Big.big_int -> location -> mach_state -> Word.int
  
  val set_location :
    Big.big_int -> location -> Word.int -> mach_state -> mach_state
 end

module RTL = 
 functor (M:MACHINE_SIG) ->
 struct 
  module AddrIndexed = 
   struct 
    type t = int
    
    (** val index : int -> Big.big_int **)
    
    let index i =
      ZIndexed.index (Word.unsigned M.size_addr i)
    
    (** val eq : Word.int -> Word.int -> bool **)
    
    let eq =
      fun _ _ -> false
   end
  
  module AddrMap = IMap(AddrIndexed)
  
  type bit_vector_op =
  | Coq_add_op
  | Coq_sub_op
  | Coq_mul_op
  | Coq_divs_op
  | Coq_divu_op
  | Coq_modu_op
  | Coq_mods_op
  | Coq_and_op
  | Coq_or_op
  | Coq_xor_op
  | Coq_shl_op
  | Coq_shr_op
  | Coq_shru_op
  | Coq_ror_op
  | Coq_rol_op
  
  (** val bit_vector_op_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bit_vector_op -> 'a1 **)
  
  let bit_vector_op_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
  | Coq_add_op -> f
  | Coq_sub_op -> f0
  | Coq_mul_op -> f1
  | Coq_divs_op -> f2
  | Coq_divu_op -> f3
  | Coq_modu_op -> f4
  | Coq_mods_op -> f5
  | Coq_and_op -> f6
  | Coq_or_op -> f7
  | Coq_xor_op -> f8
  | Coq_shl_op -> f9
  | Coq_shr_op -> f10
  | Coq_shru_op -> f11
  | Coq_ror_op -> f12
  | Coq_rol_op -> f13
  
  (** val bit_vector_op_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bit_vector_op -> 'a1 **)
  
  let bit_vector_op_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
  | Coq_add_op -> f
  | Coq_sub_op -> f0
  | Coq_mul_op -> f1
  | Coq_divs_op -> f2
  | Coq_divu_op -> f3
  | Coq_modu_op -> f4
  | Coq_mods_op -> f5
  | Coq_and_op -> f6
  | Coq_or_op -> f7
  | Coq_xor_op -> f8
  | Coq_shl_op -> f9
  | Coq_shr_op -> f10
  | Coq_shru_op -> f11
  | Coq_ror_op -> f12
  | Coq_rol_op -> f13
  
  type test_op =
  | Coq_eq_op
  | Coq_lt_op
  | Coq_ltu_op
  
  (** val test_op_rect : 'a1 -> 'a1 -> 'a1 -> test_op -> 'a1 **)
  
  let test_op_rect f f0 f1 = function
  | Coq_eq_op -> f
  | Coq_lt_op -> f0
  | Coq_ltu_op -> f1
  
  (** val test_op_rec : 'a1 -> 'a1 -> 'a1 -> test_op -> 'a1 **)
  
  let test_op_rec f f0 f1 = function
  | Coq_eq_op -> f
  | Coq_lt_op -> f0
  | Coq_ltu_op -> f1
  
  type pseudo_reg =
    Big.big_int
    (* singleton inductive, whose constructor was ps_reg *)
  
  (** val pseudo_reg_rect :
      Big.big_int -> (Big.big_int -> 'a1) -> pseudo_reg -> 'a1 **)
  
  let pseudo_reg_rect s f p =
    f p
  
  (** val pseudo_reg_rec :
      Big.big_int -> (Big.big_int -> 'a1) -> pseudo_reg -> 'a1 **)
  
  let pseudo_reg_rec s f p =
    f p
  
  type rtl_instr =
  | Coq_arith_rtl of Big.big_int * bit_vector_op * pseudo_reg * pseudo_reg
     * pseudo_reg
  | Coq_test_rtl of Big.big_int * test_op * pseudo_reg * pseudo_reg
     * pseudo_reg
  | Coq_if_rtl of pseudo_reg * rtl_instr
  | Coq_cast_s_rtl of Big.big_int * Big.big_int * pseudo_reg * pseudo_reg
  | Coq_cast_u_rtl of Big.big_int * Big.big_int * pseudo_reg * pseudo_reg
  | Coq_load_imm_rtl of Big.big_int * int * pseudo_reg
  | Coq_set_loc_rtl of Big.big_int * pseudo_reg * M.location
  | Coq_get_loc_rtl of Big.big_int * M.location * pseudo_reg
  | Coq_set_byte_rtl of pseudo_reg * pseudo_reg
  | Coq_get_byte_rtl of pseudo_reg * pseudo_reg
  | Coq_choose_rtl of Big.big_int * pseudo_reg
  | Coq_error_rtl
  | Coq_safe_fail_rtl
  
  (** val rtl_instr_rect :
      (Big.big_int -> bit_vector_op -> pseudo_reg -> pseudo_reg -> pseudo_reg
      -> 'a1) -> (Big.big_int -> test_op -> pseudo_reg -> pseudo_reg ->
      pseudo_reg -> 'a1) -> (pseudo_reg -> rtl_instr -> 'a1 -> 'a1) ->
      (Big.big_int -> Big.big_int -> pseudo_reg -> pseudo_reg -> 'a1) ->
      (Big.big_int -> Big.big_int -> pseudo_reg -> pseudo_reg -> 'a1) ->
      (Big.big_int -> int -> pseudo_reg -> 'a1) -> (Big.big_int -> pseudo_reg
      -> M.location -> 'a1) -> (Big.big_int -> M.location -> pseudo_reg ->
      'a1) -> (pseudo_reg -> pseudo_reg -> 'a1) -> (pseudo_reg -> pseudo_reg
      -> 'a1) -> (Big.big_int -> pseudo_reg -> 'a1) -> 'a1 -> 'a1 ->
      rtl_instr -> 'a1 **)
  
  let rec rtl_instr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
  | Coq_arith_rtl (s, b, r1, r2, rd) -> f s b r1 r2 rd
  | Coq_test_rtl (s, top, r1, r2, rd) -> f0 s top r1 r2 rd
  | Coq_if_rtl (p, r0) ->
    f1 p r0 (rtl_instr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 r0)
  | Coq_cast_s_rtl (s1, s2, r1, rd) -> f2 s1 s2 r1 rd
  | Coq_cast_u_rtl (s1, s2, r1, rd) -> f3 s1 s2 r1 rd
  | Coq_load_imm_rtl (s, i, rd) -> f4 s i rd
  | Coq_set_loc_rtl (s, rs, l) -> f5 s rs l
  | Coq_get_loc_rtl (s, l, rd) -> f6 s l rd
  | Coq_set_byte_rtl (rs, addr) -> f7 rs addr
  | Coq_get_byte_rtl (addr, rd) -> f8 addr rd
  | Coq_choose_rtl (s, rd) -> f9 s rd
  | Coq_error_rtl -> f10
  | Coq_safe_fail_rtl -> f11
  
  (** val rtl_instr_rec :
      (Big.big_int -> bit_vector_op -> pseudo_reg -> pseudo_reg -> pseudo_reg
      -> 'a1) -> (Big.big_int -> test_op -> pseudo_reg -> pseudo_reg ->
      pseudo_reg -> 'a1) -> (pseudo_reg -> rtl_instr -> 'a1 -> 'a1) ->
      (Big.big_int -> Big.big_int -> pseudo_reg -> pseudo_reg -> 'a1) ->
      (Big.big_int -> Big.big_int -> pseudo_reg -> pseudo_reg -> 'a1) ->
      (Big.big_int -> int -> pseudo_reg -> 'a1) -> (Big.big_int -> pseudo_reg
      -> M.location -> 'a1) -> (Big.big_int -> M.location -> pseudo_reg ->
      'a1) -> (pseudo_reg -> pseudo_reg -> 'a1) -> (pseudo_reg -> pseudo_reg
      -> 'a1) -> (Big.big_int -> pseudo_reg -> 'a1) -> 'a1 -> 'a1 ->
      rtl_instr -> 'a1 **)
  
  let rec rtl_instr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
  | Coq_arith_rtl (s, b, r1, r2, rd) -> f s b r1 r2 rd
  | Coq_test_rtl (s, top, r1, r2, rd) -> f0 s top r1 r2 rd
  | Coq_if_rtl (p, r0) ->
    f1 p r0 (rtl_instr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 r0)
  | Coq_cast_s_rtl (s1, s2, r1, rd) -> f2 s1 s2 r1 rd
  | Coq_cast_u_rtl (s1, s2, r1, rd) -> f3 s1 s2 r1 rd
  | Coq_load_imm_rtl (s, i, rd) -> f4 s i rd
  | Coq_set_loc_rtl (s, rs, l) -> f5 s rs l
  | Coq_get_loc_rtl (s, l, rd) -> f6 s l rd
  | Coq_set_byte_rtl (rs, addr) -> f7 rs addr
  | Coq_get_byte_rtl (addr, rd) -> f8 addr rd
  | Coq_choose_rtl (s, rd) -> f9 s rd
  | Coq_error_rtl -> f10
  | Coq_safe_fail_rtl -> f11
  
  type pseudo_env = Big.big_int -> pseudo_reg -> int
  
  (** val empty_env : pseudo_env **)
  
  let empty_env s x =
    Word.zero s
  
  (** val eq_pseudo_reg : Big.big_int -> pseudo_reg -> pseudo_reg -> bool **)
  
  let eq_pseudo_reg s r1 r2 =
    Z.eq_dec r1 r2
  
  (** val update_env :
      Big.big_int -> pseudo_reg -> int -> pseudo_env -> pseudo_env **)
  
  let update_env s r v env s' r' =
    let s0 = eq_nat_dec s s' in
    if s0
    then let s1 = eq_pseudo_reg s' r r' in if s1 then v else env s' r'
    else env s' r'
  
  type oracle = { oracle_bits : (Big.big_int -> Big.big_int -> int);
                  oracle_offset : Big.big_int }
  
  (** val oracle_rect :
      ((Big.big_int -> Big.big_int -> int) -> Big.big_int -> 'a1) -> oracle
      -> 'a1 **)
  
  let oracle_rect f o =
    let { oracle_bits = x; oracle_offset = x0 } = o in f x x0
  
  (** val oracle_rec :
      ((Big.big_int -> Big.big_int -> int) -> Big.big_int -> 'a1) -> oracle
      -> 'a1 **)
  
  let oracle_rec f o =
    let { oracle_bits = x; oracle_offset = x0 } = o in f x x0
  
  (** val oracle_bits : oracle -> Big.big_int -> Big.big_int -> int **)
  
  let oracle_bits o =
    o.oracle_bits
  
  (** val oracle_offset : oracle -> Big.big_int **)
  
  let oracle_offset o =
    o.oracle_offset
  
  type rtl_state = { rtl_oracle : oracle; rtl_env : pseudo_env;
                     rtl_mach_state : M.mach_state;
                     rtl_memory : int8 AddrMap.t }
  
  (** val rtl_state_rect :
      (oracle -> pseudo_env -> M.mach_state -> int8 AddrMap.t -> 'a1) ->
      rtl_state -> 'a1 **)
  
  let rtl_state_rect f r =
    let { rtl_oracle = x; rtl_env = x0; rtl_mach_state = x1; rtl_memory =
      x2 } = r
    in
    f x x0 x1 x2
  
  (** val rtl_state_rec :
      (oracle -> pseudo_env -> M.mach_state -> int8 AddrMap.t -> 'a1) ->
      rtl_state -> 'a1 **)
  
  let rtl_state_rec f r =
    let { rtl_oracle = x; rtl_env = x0; rtl_mach_state = x1; rtl_memory =
      x2 } = r
    in
    f x x0 x1 x2
  
  (** val rtl_oracle : rtl_state -> oracle **)
  
  let rtl_oracle r =
    r.rtl_oracle
  
  (** val rtl_env : rtl_state -> pseudo_env **)
  
  let rtl_env r =
    r.rtl_env
  
  (** val rtl_mach_state : rtl_state -> M.mach_state **)
  
  let rtl_mach_state r =
    r.rtl_mach_state
  
  (** val rtl_memory : rtl_state -> int8 AddrMap.t **)
  
  let rtl_memory r =
    r.rtl_memory
  
  type 'a coq_RTL_ans =
  | Fail_ans
  | SafeFail_ans
  | Okay_ans of 'a
  
  (** val coq_RTL_ans_rect :
      'a2 -> 'a2 -> ('a1 -> 'a2) -> 'a1 coq_RTL_ans -> 'a2 **)
  
  let coq_RTL_ans_rect f f0 f1 = function
  | Fail_ans -> f
  | SafeFail_ans -> f0
  | Okay_ans x -> f1 x
  
  (** val coq_RTL_ans_rec :
      'a2 -> 'a2 -> ('a1 -> 'a2) -> 'a1 coq_RTL_ans -> 'a2 **)
  
  let coq_RTL_ans_rec f f0 f1 = function
  | Fail_ans -> f
  | SafeFail_ans -> f0
  | Okay_ans x -> f1 x
  
  type 't coq_RTL = rtl_state -> 't coq_RTL_ans * rtl_state
  
  (** val coq_RTL_monad : __ coq_RTL coq_Monad **)
  
  let coq_RTL_monad =
    { coq_Return = (fun _ x rs -> ((Okay_ans x), rs)); coq_Bind =
      (fun _ _ c f rs ->
      let (r, rs') = c rs in
      (match r with
       | Okay_ans v -> f v rs'
       | x -> (x, rs'))) }
  
  (** val coq_Fail : 'a1 coq_RTL **)
  
  let coq_Fail rs =
    (Fail_ans, rs)
  
  (** val coq_SafeFail : 'a1 coq_RTL **)
  
  let coq_SafeFail rs =
    (SafeFail_ans, rs)
  
  (** val flush_env : unit coq_RTL **)
  
  let flush_env rs =
    ((Okay_ans ()), { rtl_oracle = (rtl_oracle rs); rtl_env = empty_env;
      rtl_mach_state = (rtl_mach_state rs); rtl_memory = (rtl_memory rs) })
  
  (** val set_ps : Big.big_int -> pseudo_reg -> int -> unit coq_RTL **)
  
  let set_ps s r v rs =
    ((Okay_ans ()), { rtl_oracle = (rtl_oracle rs); rtl_env =
      (update_env s r v (rtl_env rs)); rtl_mach_state = (rtl_mach_state rs);
      rtl_memory = (rtl_memory rs) })
  
  (** val set_loc : Big.big_int -> M.location -> int -> unit coq_RTL **)
  
  let set_loc s l v rs =
    ((Okay_ans ()), { rtl_oracle = (rtl_oracle rs); rtl_env = (rtl_env rs);
      rtl_mach_state = (M.set_location s l v (rtl_mach_state rs));
      rtl_memory = (rtl_memory rs) })
  
  (** val set_byte : int -> int -> unit coq_RTL **)
  
  let set_byte addr v rs =
    ((Okay_ans ()), { rtl_oracle = (rtl_oracle rs); rtl_env = (rtl_env rs);
      rtl_mach_state = (rtl_mach_state rs); rtl_memory =
      (AddrMap.set addr v (rtl_memory rs)) })
  
  (** val get_ps : Big.big_int -> pseudo_reg -> int coq_RTL **)
  
  let get_ps s r rs =
    ((Okay_ans (rtl_env rs s r)), rs)
  
  (** val get_loc : Big.big_int -> M.location -> int coq_RTL **)
  
  let get_loc s l rs =
    ((Okay_ans (M.get_location s l (rtl_mach_state rs))), rs)
  
  (** val get_byte : int -> int coq_RTL **)
  
  let get_byte addr rs =
    ((Okay_ans (AddrMap.get addr (rtl_memory rs))), rs)
  
  (** val choose_bits : Big.big_int -> int coq_RTL **)
  
  let choose_bits s rs =
    let o = rtl_oracle rs in
    let o' = { oracle_bits = (oracle_bits o); oracle_offset =
      (Z.add (oracle_offset o) Big.one) }
    in
    ((Okay_ans (oracle_bits o s (oracle_offset o))), { rtl_oracle = o';
    rtl_env = (rtl_env rs); rtl_mach_state = (rtl_mach_state rs);
    rtl_memory = (rtl_memory rs) })
  
  (** val interp_arith :
      Big.big_int -> bit_vector_op -> int -> int -> int **)
  
  let interp_arith s b v1 v2 =
    match b with
    | Coq_add_op -> Word.add s v1 v2
    | Coq_sub_op -> Word.sub s v1 v2
    | Coq_mul_op -> Word.mul s v1 v2
    | Coq_divs_op -> Word.divs s v1 v2
    | Coq_divu_op -> Word.divu s v1 v2
    | Coq_modu_op -> Word.modu s v1 v2
    | Coq_mods_op -> Word.mods s v1 v2
    | Coq_and_op -> Word.coq_and s v1 v2
    | Coq_or_op -> Word.coq_or s v1 v2
    | Coq_xor_op -> Word.xor s v1 v2
    | Coq_shl_op -> Word.shl s v1 v2
    | Coq_shr_op -> Word.shr s v1 v2
    | Coq_shru_op -> Word.shru s v1 v2
    | Coq_ror_op -> Word.ror s v1 v2
    | Coq_rol_op -> Word.rol s v1 v2
  
  (** val interp_test : Big.big_int -> test_op -> int -> int -> int **)
  
  let interp_test s t0 v1 v2 =
    if match t0 with
       | Coq_eq_op -> Word.eq s v1 v2
       | Coq_lt_op -> Word.lt s v1 v2
       | Coq_ltu_op -> Word.ltu s v1 v2
    then Word.one size1
    else Word.zero size1
  
  (** val interp_rtl : rtl_instr -> unit coq_RTL **)
  
  let rec interp_rtl = function
  | Coq_arith_rtl (s, b, r1, r2, rd) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps s r1)) (fun v1 ->
      coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps s r2)) (fun v2 ->
        set_ps s rd (interp_arith s b v1 v2)))
  | Coq_test_rtl (s, t0, r1, r2, rd) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps s r1)) (fun v1 ->
      coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps s r2)) (fun v2 ->
        set_ps size1 rd (interp_test s t0 v1 v2)))
  | Coq_if_rtl (r, i) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps size1 r)) (fun v ->
      if Word.eq size1 v (Word.one size1)
      then interp_rtl i
      else coq_Return (Obj.magic coq_RTL_monad) ())
  | Coq_cast_s_rtl (s1, s2, rs, rd) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps s1 rs)) (fun v ->
      set_ps s2 rd (Word.repr s2 (Word.signed s1 v)))
  | Coq_cast_u_rtl (s1, s2, rs, rd) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps s1 rs)) (fun v ->
      set_ps s2 rd (Word.repr s2 (Word.unsigned s1 v)))
  | Coq_load_imm_rtl (s, i, rd) -> set_ps s rd i
  | Coq_set_loc_rtl (s, rs, l) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps s rs)) (fun v ->
      set_loc s l v)
  | Coq_get_loc_rtl (s, l, rd) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_loc s l)) (fun v ->
      set_ps s rd v)
  | Coq_set_byte_rtl (rs, addr) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps size8 rs))
      (fun v ->
      coq_Bind (Obj.magic coq_RTL_monad)
        (Obj.magic (get_ps M.size_addr addr)) (fun a -> set_byte a v))
  | Coq_get_byte_rtl (addr, rd) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_ps M.size_addr addr))
      (fun a ->
      coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (get_byte a)) (fun v ->
        set_ps size8 rd v))
  | Coq_choose_rtl (s, rd) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic (choose_bits s)) (fun v ->
      set_ps s rd v)
  | Coq_error_rtl -> coq_Fail
  | Coq_safe_fail_rtl -> coq_SafeFail
  
  type instruction = { instr_assembly : char list; instr_rtl : rtl_instr list }
  
  (** val instruction_rect :
      (char list -> rtl_instr list -> 'a1) -> instruction -> 'a1 **)
  
  let instruction_rect f i =
    let { instr_assembly = x; instr_rtl = x0 } = i in f x x0
  
  (** val instruction_rec :
      (char list -> rtl_instr list -> 'a1) -> instruction -> 'a1 **)
  
  let instruction_rec f i =
    let { instr_assembly = x; instr_rtl = x0 } = i in f x x0
  
  (** val instr_assembly : instruction -> char list **)
  
  let instr_assembly i =
    i.instr_assembly
  
  (** val instr_rtl : instruction -> rtl_instr list **)
  
  let instr_rtl i =
    i.instr_rtl
 end

