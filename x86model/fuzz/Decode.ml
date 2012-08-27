open BinInt
open Bits
open Bool
open Compare_dec
open Datatypes
open List0
open MinMax
open Monad
open Peano
open Specif
open String0
open X86Syntax
open ZArith_dec
open Zdiv
open Fuzz
open X86_PARSER_ARG
open X86_PARSER
open X86_BASE_PARSER
  
  (** val coq_AAA_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_AAA_p =
    map
      (bits_n
        (length ('0'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::[]))))))))))
      instruction_t
      (bits ('0'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::[])))))))))
      (fun x -> Obj.magic AAA)
  
  (** val coq_AAD_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_AAD_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[]))))))))))))))))))
      instruction_t
      (bits
        ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))
      (fun x -> Obj.magic AAD)
  
  (** val coq_AAM_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_AAM_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[]))))))))))))))))))
      instruction_t
      (bits
        ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))
      (fun x -> Obj.magic AAM)
  
  (** val coq_AAS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_AAS_p =
    map
      (bits_n
        (length ('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::[]))))))))))
      instruction_t
      (bits ('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))
      (fun x -> Obj.magic AAS)
  
  (** val imm_op : bool -> X86_BASE_PARSER.coq_parser **)
  
  let imm_op = function
  | true ->
    map half_t operand_t halfword (fun w ->
      Obj.magic (Imm_op (sign_extend16_32 (Obj.magic w))))
  | false ->
    map word_t operand_t word (fun w -> Obj.magic (Imm_op (Obj.magic w)))
  
  (** val logic_or_arith_p :
      bool -> char list -> char list -> (bool -> operand -> operand -> instr)
      -> X86_BASE_PARSER.coq_parser **)
  
  let logic_or_arith_p opsize_override op1 op2 instCon =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))))) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))))) op1
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))))) ('0'::[])
            (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
              (operand_t, operand_t)))) anybit
              (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
                (operand_t, operand_t)) anybit modrm)))) (fun p ->
        let (d, r) = Obj.magic p in
        let (w, r0) = r in
        let (op3, op4) = r0 in
        if d
        then Obj.magic instCon w op3 op4
        else Obj.magic instCon w op4 op3))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
            ('1'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
              ('0'::('0'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                ('1'::('1'::[]))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                  op2 (seq register_t byte_t reg byte))))) (fun p ->
          let (r, imm) = Obj.magic p in
          Obj.magic instCon true (Reg_op r) (Imm_op (sign_extend8_32 imm))))
        (alt instruction_t
          (map (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
            instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
              ('1'::('0'::('0'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                ('0'::('0'::('0'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                  ('1'::('1'::[]))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                    op2 (seq register_t byte_t reg byte))))) (fun p ->
            let (r, imm) = Obj.magic p in
            Obj.magic instCon false (Reg_op r) (Imm_op (zero_extend8_32 imm))))
          (alt instruction_t
            (map (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
              instruction_t
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
                ('1'::('0'::('0'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                  operand_t)) ('0'::('0'::('0'::('1'::[]))))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                    operand_t)) ('1'::('1'::[]))
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                      operand_t)) op2
                      (seq register_t operand_t reg (imm_op opsize_override))))))
              (fun p ->
              let (r, imm) = Obj.magic p in
              Obj.magic instCon true (Reg_op r) imm))
            (alt instruction_t
              (map byte_t instruction_t
                (bitsleft byte_t op1
                  (bitsleft byte_t ('1'::('0'::('0'::[]))) byte)) (fun imm ->
                Obj.magic instCon false (Reg_op EAX) (Imm_op
                  (zero_extend8_32 (Obj.magic imm)))))
              (alt instruction_t
                (map operand_t instruction_t
                  (bitsleft operand_t op1
                    (bitsleft operand_t ('1'::('0'::('1'::[])))
                      (imm_op opsize_override))) (fun imm ->
                  Obj.magic instCon true (Reg_op EAX) imm))
                (alt instruction_t
                  (map (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
                    instruction_t
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                      byte_t)) ('1'::('0'::('0'::('0'::[]))))
                      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        byte_t)) ('0'::('0'::('0'::('0'::[]))))
                        (seq operand_t byte_t (ext_op_modrm op2) byte)))
                    (fun p ->
                    let (op, imm) = Obj.magic p in
                    Obj.magic instCon false op (Imm_op (zero_extend8_32 imm))))
                  (alt instruction_t
                    (map (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
                      instruction_t
                      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        byte_t)) ('1'::('0'::('0'::('0'::[]))))
                        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                          byte_t)) ('0'::('0'::('1'::('1'::[]))))
                          (seq operand_t byte_t (ext_op_modrm op2) byte)))
                      (fun p ->
                      let (op, imm) = Obj.magic p in
                      Obj.magic instCon true op (Imm_op
                        (sign_extend8_32 imm))))
                    (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                      instruction_t
                      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        operand_t)) ('1'::('0'::('0'::('0'::[]))))
                        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                          operand_t)) ('0'::('0'::('0'::('1'::[]))))
                          (seq operand_t operand_t (ext_op_modrm op2)
                            (imm_op opsize_override)))) (fun p ->
                      let (op, imm) = Obj.magic p in
                      Obj.magic instCon true op imm)))))))))
  
  (** val coq_ADC_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_ADC_p s =
    logic_or_arith_p s ('0'::('0'::('0'::('1'::('0'::[])))))
      ('0'::('1'::('0'::[]))) (fun x x0 x1 -> ADC (x, x0, x1))
  
  (** val coq_ADD_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_ADD_p s =
    logic_or_arith_p s ('0'::('0'::('0'::('0'::('0'::[])))))
      ('0'::('0'::('0'::[]))) (fun x x0 x1 -> ADD (x, x0, x1))
  
  (** val coq_AND_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_AND_p s =
    logic_or_arith_p s ('0'::('0'::('1'::('0'::('0'::[])))))
      ('1'::('0'::('0'::[]))) (fun x x0 x1 -> AND (x, x0, x1))
  
  (** val coq_CMP_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_CMP_p s =
    logic_or_arith_p s ('0'::('0'::('1'::('1'::('1'::[])))))
      ('1'::('1'::('1'::[]))) (fun x x0 x1 -> CMP (x, x0, x1))
  
  (** val coq_OR_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_OR_p s =
    logic_or_arith_p s ('0'::('0'::('0'::('0'::('1'::[])))))
      ('0'::('0'::('1'::[]))) (fun x x0 x1 -> OR (x, x0, x1))
  
  (** val coq_SBB_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_SBB_p s =
    logic_or_arith_p s ('0'::('0'::('0'::('1'::('1'::[])))))
      ('0'::('1'::('1'::[]))) (fun x x0 x1 -> SBB (x, x0, x1))
  
  (** val coq_SUB_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_SUB_p s =
    logic_or_arith_p s ('0'::('0'::('1'::('0'::('1'::[])))))
      ('1'::('0'::('1'::[]))) (fun x x0 x1 -> SUB (x, x0, x1))
  
  (** val coq_XOR_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_XOR_p s =
    logic_or_arith_p s ('0'::('0'::('1'::('1'::('0'::[])))))
      ('1'::('1'::('0'::[]))) (fun x x0 x1 -> XOR (x, x0, x1))
  
  (** val coq_ARPL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_ARPL_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('1'::('1'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('0'::('1'::('1'::[])))) modrm)) (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (ARPL (op1, op2)))
  
  (** val coq_BOUND_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BOUND_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('1'::('1'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('0'::('1'::('0'::[])))) modrm)) (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (BOUND (op1, op2)))
  
  (** val coq_BSF_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BSF_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('1'::('1'::('0'::('0'::[])))) modrm)))) (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (BSF (op1, op2)))
  
  (** val coq_BSR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BSR_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('1'::('1'::('0'::('1'::[])))) modrm)))) (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (BSR (op1, op2)))
  
  (** val coq_BSWAP_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BSWAP_p =
    map register_t instruction_t
      (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft register_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft register_t ('1'::('1'::('0'::('0'::[]))))
            (bitsleft register_t ('1'::[]) reg)))) (fun x ->
      Obj.magic (BSWAP (Obj.magic x)))
  
  (** val bit_test_p :
      char list -> char list -> (operand -> operand -> instr) ->
      X86_BASE_PARSER.coq_parser **)
  
  let bit_test_p opcode1 opcode2 instr0 =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
              ('1'::('0'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                ('1'::('0'::('1'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                  ('1'::('1'::[]))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                    opcode1 (seq register_t byte_t reg byte))))))) (fun p ->
        let (r, imm) = Obj.magic p in
        Obj.magic instr0 (Reg_op r) (Imm_op (zero_extend8_32 imm))))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
                ('1'::('0'::('1'::('1'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
                  ('1'::('0'::('1'::('0'::[]))))
                  (seq operand_t byte_t (ext_op_modrm opcode1) byte)))))
          (fun p ->
          let (op1, imm) = Obj.magic p in
          Obj.magic instr0 op1 (Imm_op (zero_extend8_32 imm))))
        (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                ('1'::('0'::('1'::[])))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                  opcode2
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                    operand_t)) ('0'::('1'::('1'::[]))) modrm))))) (fun p ->
          let (op2, op1) = Obj.magic p in Obj.magic instr0 op1 op2)))
  
  (** val coq_BT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BT_p =
    bit_test_p ('1'::('0'::('0'::[]))) ('0'::('0'::[])) (fun x x0 -> BT (x,
      x0))
  
  (** val coq_BTC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BTC_p =
    bit_test_p ('1'::('1'::('1'::[]))) ('1'::('1'::[])) (fun x x0 -> BTC (x,
      x0))
  
  (** val coq_BTR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BTR_p =
    bit_test_p ('1'::('1'::('0'::[]))) ('1'::('0'::[])) (fun x x0 -> BTR (x,
      x0))
  
  (** val coq_BTS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BTS_p =
    bit_test_p ('1'::('0'::('1'::[]))) ('0'::('1'::[])) (fun x x0 -> BTS (x,
      x0))
  
  (** val coq_CALL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CALL_p =
    alt instruction_t
      (map word_t instruction_t
        (bitsleft word_t ('1'::('1'::('1'::('0'::[]))))
          (bitsleft word_t ('1'::('0'::('0'::('0'::[])))) word)) (fun w ->
        Obj.magic (CALL (true, false, (Imm_op (Obj.magic w)), None))))
      (alt instruction_t
        (map operand_t instruction_t
          (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
              (ext_op_modrm ('0'::('1'::('0'::[])))))) (fun op ->
          Obj.magic (CALL (true, true, (Obj.magic op), None))))
        (alt instruction_t
          (map (X86_BASE_PARSER.Coq_pair_t (half_t, word_t)) instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (half_t, word_t))
              ('1'::('0'::('0'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (half_t, word_t))
                ('1'::('0'::('1'::('0'::[]))))
                (seq half_t word_t halfword word))) (fun p ->
            Obj.magic (CALL (false, false, (Imm_op (snd (Obj.magic p))),
              (Some (fst (Obj.magic p)))))))
          (map operand_t instruction_t
            (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
              (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
                (ext_op_modrm ('0'::('1'::('1'::[])))))) (fun op ->
            Obj.magic (CALL (false, true, (Obj.magic op), None))))))
  
  (** val coq_CDQ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CDQ_p =
    map (bits_n (length ('1'::('0'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
        ('1'::('0'::('0'::('1'::[])))) (bits ('1'::('0'::('0'::('1'::[]))))))
      (fun x -> Obj.magic CDQ)
  
  (** val coq_CLC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CLC_p =
    map (bits_n (length ('1'::('0'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('1'::('0'::('0'::('0'::[]))))))
      (fun x -> Obj.magic CLC)
  
  (** val coq_CLD_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CLD_p =
    map (bits_n (length ('1'::('1'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('0'::('0'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('1'::('1'::('0'::('0'::[]))))))
      (fun x -> Obj.magic CLD)
  
  (** val coq_CLI_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CLI_p =
    map (bits_n (length ('1'::('0'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('1'::('0'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('1'::('0'::('1'::('0'::[]))))))
      (fun x -> Obj.magic CLI)
  
  (** val coq_CLTS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CLTS_p =
    map (bits_n (length ('0'::('1'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bits ('0'::('1'::('1'::('0'::[])))))))) (fun x ->
      Obj.magic CLTS)
  
  (** val coq_CMC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CMC_p =
    map (bits_n (length ('0'::('1'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('1'::('0'::('1'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('0'::('1'::('0'::('1'::[]))))))
      (fun x -> Obj.magic CMC)
  
  (** val coq_CMPS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CMPS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('0'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('0'::('1'::('1'::[]))) anybit))
      (fun x -> Obj.magic (CMPS (Obj.magic x)))
  
  (** val coq_CMPXCHG_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CMPXCHG_p =
    map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
              (operand_t, operand_t)))) ('0'::('0'::('0'::[])))
              (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
                (operand_t, operand_t)) anybit modrm))))) (fun p ->
      let (w, r) = Obj.magic p in
      let (op1, op2) = r in Obj.magic (CMPXCHG (w, op2, op1)))
  
  (** val coq_CPUID_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CPUID_p =
    map (bits_n (length ('0'::('0'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
            ('1'::('0'::('1'::('0'::[]))))
            (bits ('0'::('0'::('1'::('0'::[])))))))) (fun x ->
      Obj.magic CPUID)
  
  (** val coq_CWDE_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CWDE_p =
    map (bits_n (length ('1'::('0'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
        ('1'::('0'::('0'::('1'::[])))) (bits ('1'::('0'::('0'::('0'::[]))))))
      (fun x -> Obj.magic CWDE)
  
  (** val coq_DAA_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_DAA_p =
    map (bits_n (length ('0'::('1'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('1'::('1'::('1'::[]))))))
        ('0'::('0'::('1'::('0'::[])))) (bits ('0'::('1'::('1'::('1'::[]))))))
      (fun x -> Obj.magic DAA)
  
  (** val coq_DAS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_DAS_p =
    map (bits_n (length ('1'::('1'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('1'::('1'::[]))))))
        ('0'::('0'::('1'::('0'::[])))) (bits ('1'::('1'::('1'::('1'::[]))))))
      (fun x -> Obj.magic DAS)
  
  (** val coq_DEC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_DEC_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        register_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          register_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            register_t)) ('1'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t register_t anybit
              (bitsleft register_t ('1'::('1'::('0'::('0'::('1'::[]))))) reg))))
        (fun p ->
        let (w, r) = Obj.magic p in Obj.magic (DEC (w, (Reg_op r)))))
      (alt instruction_t
        (map register_t instruction_t
          (bitsleft register_t ('0'::('1'::('0'::('0'::[]))))
            (bitsleft register_t ('1'::[]) reg)) (fun r ->
          Obj.magic (DEC (true, (Reg_op (Obj.magic r))))))
        (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, operand_t))
              ('1'::('1'::('1'::[])))
              (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
                (ext_op_modrm ('0'::('0'::('1'::[]))))))) (fun p ->
          let (w, op1) = Obj.magic p in Obj.magic (DEC (w, op1)))))
  
  (** val coq_DIV_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_DIV_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        register_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          register_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            register_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t register_t anybit
              (bitsleft register_t ('1'::('1'::('1'::('1'::('0'::[]))))) reg))))
        (fun p ->
        let (w, r) = Obj.magic p in Obj.magic (DIV (w, (Reg_op r)))))
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
              (ext_op_modrm ('1'::('1'::('0'::[]))))))) (fun p ->
        let (w, op1) = Obj.magic p in Obj.magic (DIV (w, op1))))
  
  (** val coq_HLT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_HLT_p =
    map (bits_n (length ('0'::('1'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('1'::('0'::('0'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('0'::('1'::('0'::('0'::[]))))))
      (fun x -> Obj.magic HLT)
  
  (** val coq_IDIV_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_IDIV_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        register_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          register_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            register_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t register_t anybit
              (bitsleft register_t ('1'::('1'::('1'::('1'::('1'::[]))))) reg))))
        (fun p ->
        let (w, r) = Obj.magic p in Obj.magic (IDIV (w, (Reg_op r)))))
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
              (ext_op_modrm ('1'::('1'::('1'::[]))))))) (fun p ->
        let (w, op1) = Obj.magic p in Obj.magic (IDIV (w, op1))))
  
  (** val coq_IMUL_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_IMUL_p opsize_override =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
              (ext_op_modrm2 ('1'::('0'::('1'::[]))))))) (fun p ->
        let (w, op1) = Obj.magic p in Obj.magic (IMUL (w, op1, None, None))))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                ('1'::('0'::('1'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                  ('1'::('1'::('1'::('1'::[])))) modrm)))) (fun p ->
          let (op1, op2) = Obj.magic p in
          Obj.magic (IMUL (true, op1, (Some op2), None))))
        (alt instruction_t
          (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
            (operand_t, operand_t)), byte_t)) instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)), byte_t))
              ('0'::('1'::('1'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t
                ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                byte_t)) ('1'::('0'::('1'::('1'::[]))))
                (seq (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                  byte_t modrm byte))) (fun p ->
            let (r, imm) = Obj.magic p in
            let (op1, op2) = r in
            Obj.magic (IMUL (true, op1, (Some op2), (Some
              (sign_extend8_32 imm))))))
          (if opsize_override
           then map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
                  (operand_t, operand_t)), half_t)) instruction_t
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t
                    ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                    half_t)) ('0'::('1'::('1'::('0'::[]))))
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t
                      ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                      half_t)) ('1'::('0'::('0'::('1'::[]))))
                      (seq (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        operand_t)) half_t modrm halfword))) (fun p ->
                  let (r, imm) = Obj.magic p in
                  let (op1, op2) = r in
                  Obj.magic (IMUL (true, op1, (Some op2), (Some
                    (sign_extend16_32 imm)))))
           else map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
                  (operand_t, operand_t)), word_t)) instruction_t
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t
                    ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                    word_t)) ('0'::('1'::('1'::('0'::[]))))
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t
                      ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                      word_t)) ('1'::('0'::('0'::('1'::[]))))
                      (seq (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        operand_t)) word_t modrm word))) (fun p ->
                  let (r, imm) = Obj.magic p in
                  let (op1, op2) = r in
                  Obj.magic (IMUL (true, op1, (Some op2), (Some imm)))))))
  
  (** val coq_IN_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_IN_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t, byte_t))
        instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          byte_t)) ('1'::('1'::('1'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            byte_t)) ('0'::('1'::('0'::[])))
            (seq X86_BASE_PARSER.Coq_char_t byte_t anybit byte))) (fun p ->
        let (w, pt) = Obj.magic p in Obj.magic (IN (w, (Some pt)))))
      (map X86_BASE_PARSER.Coq_char_t instruction_t
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('1'::('0'::[]))))
          (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('0'::[])))
            anybit)) (fun w -> Obj.magic (IN ((Obj.magic w), None))))
  
  (** val coq_INC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INC_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        register_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          register_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            register_t)) ('1'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t register_t anybit
              (bitsleft register_t ('1'::('1'::('0'::('0'::('0'::[]))))) reg))))
        (fun p ->
        let (w, r) = Obj.magic p in Obj.magic (INC (w, (Reg_op r)))))
      (alt instruction_t
        (map register_t instruction_t
          (bitsleft register_t ('0'::('1'::('0'::('0'::[]))))
            (bitsleft register_t ('0'::[]) reg)) (fun r ->
          Obj.magic (INC (true, (Reg_op (Obj.magic r))))))
        (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, operand_t))
              ('1'::('1'::('1'::[])))
              (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
                (ext_op_modrm ('0'::('0'::('0'::[]))))))) (fun p ->
          let (w, op1) = Obj.magic p in Obj.magic (INC (w, op1)))))
  
  (** val coq_INS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('0'::('1'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('0'::[]))) anybit))
      (fun x -> Obj.magic (INS (Obj.magic x)))
  
  (** val coq_INTn_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INTn_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('0'::('0'::[]))))
        (bitsleft byte_t ('1'::('1'::('0'::('1'::[])))) byte)) (fun x ->
      Obj.magic (INTn (Obj.magic x)))
  
  (** val coq_INT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INT_p =
    map (bits_n (length ('1'::('1'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('0'::('0'::[]))))))
        ('1'::('1'::('0'::('0'::[])))) (bits ('1'::('1'::('0'::('0'::[]))))))
      (fun x -> Obj.magic INT)
  
  (** val coq_INTO_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INTO_p =
    map (bits_n (length ('1'::('1'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('1'::('0'::[]))))))
        ('1'::('1'::('0'::('0'::[])))) (bits ('1'::('1'::('1'::('0'::[]))))))
      (fun x -> Obj.magic INTO)
  
  (** val coq_INVD_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INVD_p =
    map (bits_n (length ('1'::('0'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bits ('1'::('0'::('0'::('0'::[])))))))) (fun x ->
      Obj.magic INVD)
  
  (** val coq_INVLPG_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INVLPG_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm ('1'::('1'::('1'::[])))))))) (fun x ->
      Obj.magic (INVLPG (Obj.magic x)))
  
  (** val coq_IRET_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_IRET_p =
    map (bits_n (length ('1'::('1'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('1'::('1'::[]))))))
        ('1'::('1'::('0'::('0'::[])))) (bits ('1'::('1'::('1'::('1'::[]))))))
      (fun x -> Obj.magic IRET)
  
  (** val coq_Jcc_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_Jcc_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (condition_t, byte_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t, byte_t))
          ('0'::('1'::('1'::('1'::[])))) (seq condition_t byte_t tttn byte))
        (fun p ->
        let (ct, imm) = Obj.magic p in
        Obj.magic (Jcc (ct, (sign_extend8_32 imm)))))
      (map (X86_BASE_PARSER.Coq_pair_t (condition_t, word_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t, word_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t, word_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t, word_t))
              ('1'::('0'::('0'::('0'::[]))))
              (seq condition_t word_t tttn word)))) (fun p ->
        let (ct, imm) = Obj.magic p in Obj.magic (Jcc (ct, imm))))
  
  (** val coq_JCXZ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_JCXZ_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
        (bitsleft byte_t ('0'::('0'::('1'::('1'::[])))) byte)) (fun x ->
      Obj.magic (JCXZ (Obj.magic x)))
  
  (** val coq_JMP_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_JMP_p =
    alt instruction_t
      (map byte_t instruction_t
        (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
          (bitsleft byte_t ('1'::('0'::('1'::('1'::[])))) byte)) (fun b ->
        Obj.magic (JMP (true, false, (Imm_op
          (sign_extend8_32 (Obj.magic b))), None))))
      (alt instruction_t
        (map word_t instruction_t
          (bitsleft word_t ('1'::('1'::('1'::('0'::[]))))
            (bitsleft word_t ('1'::('0'::('0'::('1'::[])))) word)) (fun w ->
          Obj.magic (JMP (true, false, (Imm_op (Obj.magic w)), None))))
        (alt instruction_t
          (map operand_t instruction_t
            (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
              (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
                (ext_op_modrm2 ('1'::('0'::('0'::[])))))) (fun op ->
            Obj.magic (JMP (true, true, (Obj.magic op), None))))
          (alt instruction_t
            (map (X86_BASE_PARSER.Coq_pair_t (half_t, word_t)) instruction_t
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (half_t, word_t))
                ('1'::('1'::('1'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (half_t, word_t))
                  ('1'::('0'::('1'::('0'::[]))))
                  (seq half_t word_t halfword word))) (fun p ->
              Obj.magic (JMP (false, true, (Imm_op (snd (Obj.magic p))),
                (Some (fst (Obj.magic p)))))))
            (map operand_t instruction_t
              (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
                (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
                  (ext_op_modrm2 ('1'::('0'::('1'::[])))))) (fun op ->
              Obj.magic (JMP (false, true, (Obj.magic op), None)))))))
  
  (** val coq_LAHF_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LAHF_p =
    map (bits_n (length ('1'::('1'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('1'::('1'::[]))))))
        ('1'::('0'::('0'::('1'::[])))) (bits ('1'::('1'::('1'::('1'::[]))))))
      (fun x -> Obj.magic LAHF)
  
  (** val coq_LAR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LAR_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('0'::('1'::('0'::[])))) modrm)))) (fun p ->
      Obj.magic (LAR ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LDS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LDS_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('1'::('1'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('1'::('0'::('1'::[])))) modrm)) (fun p ->
      Obj.magic (LDS ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LEA_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LEA_p =
    map (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
        ('1'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
          ('1'::('1'::('0'::('1'::[])))) modrm_noreg)) (fun p ->
      Obj.magic (LEA ((Reg_op (fst (Obj.magic p))), (snd (Obj.magic p)))))
  
  (** val coq_LEAVE_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LEAVE_p =
    map (bits_n (length ('1'::('0'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
        ('1'::('1'::('0'::('0'::[])))) (bits ('1'::('0'::('0'::('1'::[]))))))
      (fun x -> Obj.magic LEAVE)
  
  (** val coq_LES_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LES_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('1'::('1'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('1'::('0'::('0'::[])))) modrm)) (fun p ->
      Obj.magic (LES ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LFS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LFS_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('1'::('0'::('0'::[])))) modrm)))) (fun p ->
      Obj.magic (LFS ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LGDT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LGDT_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm ('0'::('1'::('0'::[])))))))) (fun x ->
      Obj.magic (LGDT (Obj.magic x)))
  
  (** val coq_LGS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LGS_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('1'::('0'::('1'::[])))) modrm)))) (fun p ->
      Obj.magic (LGS ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LIDT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LIDT_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm ('0'::('1'::('1'::[])))))))) (fun x ->
      Obj.magic (LIDT (Obj.magic x)))
  
  (** val coq_LLDT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LLDT_p =
    alt instruction_t
      (map register_t instruction_t
        (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
          (bitsleft register_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
              (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
                (bitsleft register_t ('1'::('1'::[]))
                  (bitsleft register_t ('0'::('1'::('0'::[]))) reg))))))
        (fun r -> Obj.magic (LLDT (Reg_op (Obj.magic r)))))
      (map operand_t instruction_t
        (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
          (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
                (ext_op_modrm ('0'::('1'::('0'::[])))))))) (fun x ->
        Obj.magic (LLDT (Obj.magic x))))
  
  (** val coq_LMSW_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LMSW_p =
    alt instruction_t
      (map register_t instruction_t
        (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
          (bitsleft register_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
              (bitsleft register_t ('0'::('0'::('0'::('1'::[]))))
                (bitsleft register_t ('1'::('1'::[]))
                  (bitsleft register_t ('1'::('1'::('0'::[]))) reg))))))
        (fun r -> Obj.magic (LMSW (Reg_op (Obj.magic r)))))
      (map operand_t instruction_t
        (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
          (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
                (bitsleft operand_t ('1'::('1'::[]))
                  (ext_op_modrm ('1'::('1'::('0'::[]))))))))) (fun x ->
        Obj.magic (LMSW (Obj.magic x))))
  
  (** val coq_LODS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LODS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('0'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('0'::[]))) anybit))
      (fun x -> Obj.magic (LODS (Obj.magic x)))

  (***** NOTE: for fuzzing these, we want to make the byte offset tiny, or else there will be issues *)
  
  (** val coq_LOOP_p : X86_BASE_PARSER.coq_parser **)
 
  let coq_LOOP_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
        (bitsleft byte_t ('0'::('0'::('1'::('0'::[])))) byte)) (fun x ->
      Obj.magic (LOOP (Obj.magic x)))
  
  (** val coq_LOOPZ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LOOPZ_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
        (bitsleft byte_t ('0'::('0'::('0'::('1'::[])))) byte)) (fun x ->
      Obj.magic (LOOPZ (Obj.magic x)))
  
  (** val coq_LOOPNZ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LOOPNZ_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
        (bitsleft byte_t ('0'::('0'::('0'::('0'::[])))) byte)) (fun x ->
      Obj.magic (LOOPNZ (Obj.magic x)))
  
  (** val coq_LSL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LSL_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('0'::('1'::('1'::[])))) modrm)))) (fun p ->
      Obj.magic (LSL ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LSS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LSS_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('0'::('1'::('0'::[])))) modrm)))) (fun p ->
      Obj.magic (LSS ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LTR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LTR_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm ('0'::('1'::('1'::[])))))))) (fun x ->
      Obj.magic (LTR (Obj.magic x)))
  
  (** val coq_CMOVcc_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CMOVcc_p =
    map (X86_BASE_PARSER.Coq_pair_t (condition_t, (X86_BASE_PARSER.Coq_pair_t
      (operand_t, operand_t)))) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            ('0'::('1'::('0'::('0'::[]))))
            (seq condition_t (X86_BASE_PARSER.Coq_pair_t (operand_t,
              operand_t)) tttn modrm)))) (fun p ->
      let (tttn0, r) = Obj.magic p in
      let (op1, op2) = r in Obj.magic (CMOVcc (tttn0, op1, op2)))
  
  (** val coq_MOV_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_MOV_p opsize_override =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
          ('1'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            ('1'::('0'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
              (operand_t, operand_t)) anybit modrm))) (fun p ->
        let (w, r) = Obj.magic p in
        let (op1, op2) = r in Obj.magic (MOV (w, op1, op2))))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            ('1'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
              (operand_t, operand_t)))) ('1'::('0'::('0'::[])))
              (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
                (operand_t, operand_t)) anybit modrm))) (fun p ->
          let (w, r) = Obj.magic p in
          let (op1, op2) = r in Obj.magic (MOV (w, op2, op1))))
        (alt instruction_t
          (map (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
            instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
              ('1'::('1'::('0'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
                ('0'::('1'::('1'::('1'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                  operand_t)) ('1'::('1'::[]))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                    operand_t)) ('0'::('0'::('0'::[])))
                    (seq register_t operand_t reg (imm_op opsize_override))))))
            (fun p ->
            let (r, w) = Obj.magic p in Obj.magic (MOV (true, (Reg_op r), w))))
          (alt instruction_t
            (map (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
              instruction_t
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                ('1'::('1'::('0'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                  ('0'::('1'::('1'::('0'::[]))))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                    ('1'::('1'::[]))
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                      byte_t)) ('0'::('0'::('0'::[])))
                      (seq register_t byte_t reg byte))))) (fun p ->
              let (r, b) = Obj.magic p in
              Obj.magic (MOV (false, (Reg_op r), (Imm_op
                (zero_extend8_32 b))))))
            (alt instruction_t
              (map (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
                instruction_t
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                  operand_t)) ('1'::('0'::('1'::('1'::[]))))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                    operand_t)) ('1'::[])
                    (seq register_t operand_t reg (imm_op opsize_override))))
                (fun p ->
                let (r, w) = Obj.magic p in
                Obj.magic (MOV (true, (Reg_op r), w))))
              (alt instruction_t
                (map (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                  instruction_t
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                    ('1'::('0'::('1'::('1'::[]))))
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                      byte_t)) ('0'::[]) (seq register_t byte_t reg byte)))
                  (fun p ->
                  let (r, b) = Obj.magic p in
                  Obj.magic (MOV (false, (Reg_op r), (Imm_op
                    (zero_extend8_32 b))))))
                (alt instruction_t
                  (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                    instruction_t
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                      operand_t)) ('1'::('1'::('0'::('0'::[]))))
                      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        operand_t)) ('0'::('1'::('1'::('1'::[]))))
                        (seq operand_t operand_t
                          (ext_op_modrm ('0'::('0'::('0'::[]))))
                          (imm_op opsize_override)))) (fun p ->
                    let (op, w) = Obj.magic p in
                    Obj.magic (MOV (true, op, w))))
                  (alt instruction_t
                    (map (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
                      instruction_t
                      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        byte_t)) ('1'::('1'::('0'::('0'::[]))))
                        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                          byte_t)) ('0'::('1'::('1'::('0'::[]))))
                          (seq operand_t byte_t
                            (ext_op_modrm ('0'::('0'::('0'::[])))) byte)))
                      (fun p ->
                      let (op, b) = Obj.magic p in
                      Obj.magic (MOV (false, op, (Imm_op
                        (zero_extend8_32 b))))))
                    (alt instruction_t
                      (map word_t instruction_t
                        (bitsleft word_t ('1'::('0'::('1'::('0'::[]))))
                          (bitsleft word_t ('0'::('0'::('0'::('1'::[]))))
                            word)) (fun w ->
                        Obj.magic (MOV (true, (Reg_op EAX), (Offset_op
                          (Obj.magic w))))))
                      (alt instruction_t
                        (map word_t instruction_t
                          (bitsleft word_t ('1'::('0'::('1'::('0'::[]))))
                            (bitsleft word_t ('0'::('0'::('0'::('0'::[]))))
                              word)) (fun w ->
                          Obj.magic (MOV (false, (Reg_op EAX), (Offset_op
                            (Obj.magic w))))))
                        (alt instruction_t
                          (map word_t instruction_t
                            (bitsleft word_t ('1'::('0'::('1'::('0'::[]))))
                              (bitsleft word_t ('0'::('0'::('1'::('1'::[]))))
                                word)) (fun w ->
                            Obj.magic (MOV (true, (Offset_op (Obj.magic w)),
                              (Reg_op EAX)))))
                          (map word_t instruction_t
                            (bitsleft word_t ('1'::('0'::('1'::('0'::[]))))
                              (bitsleft word_t ('0'::('0'::('1'::('0'::[]))))
                                word)) (fun w ->
                            Obj.magic (MOV (false, (Offset_op (Obj.magic w)),
                              (Reg_op EAX)))))))))))))))
  
  (** val control_reg_p : X86_BASE_PARSER.coq_parser **)
  
  let control_reg_p =
    alt control_register_t
      (map (bits_n (length ('0'::('0'::('0'::[]))))) control_register_t
        (bits ('0'::('0'::('0'::[])))) (fun x -> Obj.magic CR0))
      (alt control_register_t
        (map (bits_n (length ('0'::('1'::('0'::[]))))) control_register_t
          (bits ('0'::('1'::('0'::[])))) (fun x -> Obj.magic CR2))
        (alt control_register_t
          (map (bits_n (length ('0'::('1'::('1'::[]))))) control_register_t
            (bits ('0'::('1'::('1'::[])))) (fun x -> Obj.magic CR3))
          (map (bits_n (length ('1'::('0'::('0'::[]))))) control_register_t
            (bits ('1'::('0'::('0'::[])))) (fun x -> Obj.magic CR4))))
  
  (** val coq_MOVCR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVCR_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (control_register_t, register_t))
        instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
          register_t)) ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
            register_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
              register_t)) ('0'::('0'::('1'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
                register_t)) ('0'::('0'::('1'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
                  register_t)) ('1'::('1'::[]))
                  (seq control_register_t register_t control_reg_p reg))))))
        (fun p ->
        Obj.magic (MOVCR (false, (fst (Obj.magic p)), (snd (Obj.magic p))))))
      (map (X86_BASE_PARSER.Coq_pair_t (control_register_t, register_t))
        instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
          register_t)) ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
            register_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
              register_t)) ('0'::('0'::('1'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
                register_t)) ('0'::('0'::('0'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (control_register_t,
                  register_t)) ('1'::('1'::[]))
                  (seq control_register_t register_t control_reg_p reg))))))
        (fun p ->
        Obj.magic (MOVCR (true, (fst (Obj.magic p)), (snd (Obj.magic p))))))
  
  (** val debug_reg_p : X86_BASE_PARSER.coq_parser **)
  
  let debug_reg_p =
    alt debug_register_t
      (map (bits_n (length ('0'::('0'::('0'::[]))))) debug_register_t
        (bits ('0'::('0'::('0'::[])))) (fun x -> Obj.magic DR0))
      (alt debug_register_t
        (map (bits_n (length ('0'::('0'::('1'::[]))))) debug_register_t
          (bits ('0'::('0'::('1'::[])))) (fun x -> Obj.magic DR1))
        (alt debug_register_t
          (map (bits_n (length ('0'::('1'::('0'::[]))))) debug_register_t
            (bits ('0'::('1'::('0'::[])))) (fun x -> Obj.magic DR2))
          (alt debug_register_t
            (map (bits_n (length ('0'::('1'::('1'::[]))))) debug_register_t
              (bits ('0'::('1'::('1'::[])))) (fun x -> Obj.magic DR3))
            (alt debug_register_t
              (map (bits_n (length ('1'::('1'::('0'::[]))))) debug_register_t
                (bits ('1'::('1'::('0'::[])))) (fun x -> Obj.magic DR6))
              (map (bits_n (length ('1'::('1'::('1'::[]))))) debug_register_t
                (bits ('1'::('1'::('1'::[])))) (fun x -> Obj.magic DR7))))))
  
  (** val coq_MOVDR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVDR_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (debug_register_t, register_t))
        instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t, register_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t,
            register_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t,
              register_t)) ('0'::('0'::('1'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t,
                register_t)) ('0'::('0'::('1'::('1'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t,
                  register_t)) ('1'::('1'::[]))
                  (seq debug_register_t register_t debug_reg_p reg))))))
        (fun p ->
        Obj.magic (MOVDR (false, (fst (Obj.magic p)), (snd (Obj.magic p))))))
      (map (X86_BASE_PARSER.Coq_pair_t (debug_register_t, register_t))
        instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t, register_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t,
            register_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t,
              register_t)) ('0'::('0'::('1'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t,
                register_t)) ('0'::('0'::('0'::('1'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (debug_register_t,
                  register_t)) ('1'::('1'::[]))
                  (seq debug_register_t register_t debug_reg_p reg))))))
        (fun p ->
        Obj.magic (MOVDR (true, (fst (Obj.magic p)), (snd (Obj.magic p))))))
  
  (** val segment_reg_p : X86_BASE_PARSER.coq_parser **)
  
  let segment_reg_p =
    alt segment_register_t
      (map (bits_n (length ('0'::('0'::('0'::[]))))) segment_register_t
        (bits ('0'::('0'::('0'::[])))) (fun x -> Obj.magic ES))
      (alt segment_register_t
        (map (bits_n (length ('0'::('0'::('1'::[]))))) segment_register_t
          (bits ('0'::('0'::('1'::[])))) (fun x -> Obj.magic CS))
        (alt segment_register_t
          (map (bits_n (length ('0'::('1'::('0'::[]))))) segment_register_t
            (bits ('0'::('1'::('0'::[])))) (fun x -> Obj.magic SS))
          (alt segment_register_t
            (map (bits_n (length ('0'::('1'::('1'::[]))))) segment_register_t
              (bits ('0'::('1'::('1'::[])))) (fun x -> Obj.magic DS))
            (alt segment_register_t
              (map (bits_n (length ('1'::('0'::('0'::[])))))
                segment_register_t (bits ('1'::('0'::('0'::[])))) (fun x ->
                Obj.magic FS))
              (map (bits_n (length ('1'::('0'::('1'::[])))))
                segment_register_t (bits ('1'::('0'::('1'::[])))) (fun x ->
                Obj.magic GS))))))
  
  (** val seg_modrm : X86_BASE_PARSER.coq_parser **)
  
  let seg_modrm =
    alt (X86_BASE_PARSER.Coq_pair_t (segment_register_t, operand_t))
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (segment_register_t, operand_t))
        ('0'::('0'::[]))
        (seq segment_register_t operand_t segment_reg_p rm00))
      (alt (X86_BASE_PARSER.Coq_pair_t (segment_register_t, operand_t))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (segment_register_t,
          operand_t)) ('0'::('1'::[]))
          (seq segment_register_t operand_t segment_reg_p rm01))
        (alt (X86_BASE_PARSER.Coq_pair_t (segment_register_t, operand_t))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (segment_register_t,
            operand_t)) ('1'::('0'::[]))
            (seq segment_register_t operand_t segment_reg_p rm10))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (segment_register_t,
            operand_t)) ('1'::('1'::[]))
            (seq segment_register_t operand_t segment_reg_p rm11))))
  
  (** val coq_MOVSR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVSR_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (segment_register_t, operand_t))
        instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (segment_register_t,
          operand_t)) ('1'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (segment_register_t,
            operand_t)) ('1'::('1'::('1'::('0'::[])))) seg_modrm)) (fun p ->
        Obj.magic (MOVSR (false, (fst (Obj.magic p)), (snd (Obj.magic p))))))
      (map (X86_BASE_PARSER.Coq_pair_t (segment_register_t, operand_t))
        instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (segment_register_t,
          operand_t)) ('1'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (segment_register_t,
            operand_t)) ('1'::('1'::('0'::('0'::[])))) seg_modrm)) (fun p ->
        Obj.magic (MOVSR (true, (fst (Obj.magic p)), (snd (Obj.magic p))))))
  
  (** val coq_MOVBE_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVBE_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('0'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                ('1'::('0'::('0'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                  ('1'::('1'::('1'::('1'::[]))))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                    operand_t)) ('0'::('0'::('0'::('0'::[])))) modrm))))))
        (fun p ->
        Obj.magic (MOVBE ((snd (Obj.magic p)), (fst (Obj.magic p))))))
      (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('0'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                ('1'::('0'::('0'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                  ('1'::('1'::('1'::('1'::[]))))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                    operand_t)) ('0'::('0'::('0'::('1'::[])))) modrm))))))
        (fun p ->
        Obj.magic (MOVBE ((fst (Obj.magic p)), (snd (Obj.magic p))))))
  
  (** val coq_MOVS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('0'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('0'::('1'::('0'::[]))) anybit))
      (fun x -> Obj.magic (MOVS (Obj.magic x)))
  
  (** val coq_MOVSX_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVSX_p =
    map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
              (operand_t, operand_t)))) ('1'::('1'::('1'::[])))
              (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
                (operand_t, operand_t)) anybit modrm))))) (fun p ->
      let (w, r) = Obj.magic p in
      let (op1, op2) = r in Obj.magic (MOVSX (w, op1, op2)))
  
  (** val coq_MOVZX_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVZX_p =
    map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
              (operand_t, operand_t)))) ('0'::('1'::('1'::[])))
              (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
                (operand_t, operand_t)) anybit modrm))))) (fun p ->
      let (w, r) = Obj.magic p in
      let (op1, op2) = r in Obj.magic (MOVZX (w, op1, op2)))
  
  (** val coq_MUL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MUL_p =
    map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t, operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) ('1'::('1'::('1'::('1'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('0'::('1'::('1'::[])))
          (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
            (ext_op_modrm2 ('1'::('0'::('0'::[]))))))) (fun p ->
      Obj.magic (MUL ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_NEG_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_NEG_p =
    map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t, operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) ('1'::('1'::('1'::('1'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('0'::('1'::('1'::[])))
          (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
            (ext_op_modrm2 ('0'::('1'::('1'::[]))))))) (fun p ->
      Obj.magic (NEG ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_NOT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_NOT_p =
    map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t, operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) ('1'::('1'::('1'::('1'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('0'::('1'::('1'::[])))
          (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
            (ext_op_modrm2 ('0'::('1'::('0'::[]))))))) (fun p ->
      Obj.magic (NOT ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_OUT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_OUT_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t, byte_t))
        instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          byte_t)) ('1'::('1'::('1'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            byte_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t byte_t anybit byte))) (fun p ->
        Obj.magic (OUT ((fst (Obj.magic p)), (Some (snd (Obj.magic p)))))))
      (map X86_BASE_PARSER.Coq_char_t instruction_t
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('1'::('0'::[]))))
          (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('1'::[])))
            anybit)) (fun w -> Obj.magic (OUT ((Obj.magic w), None))))
  
  (** val coq_OUTS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_OUTS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('0'::('1'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('1'::[]))) anybit))
      (fun x -> Obj.magic (OUTS (Obj.magic x)))
  
  (** val coq_POP_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_POP_p =
    alt instruction_t
      (map operand_t instruction_t
        (bitsleft operand_t ('1'::('0'::('0'::('0'::[]))))
          (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
            (ext_op_modrm ('0'::('0'::('0'::[])))))) (fun x ->
        Obj.magic (POP (Obj.magic x))))
      (map register_t instruction_t
        (bitsleft register_t ('0'::('1'::('0'::('1'::[]))))
          (bitsleft register_t ('1'::[]) reg)) (fun r ->
        Obj.magic (POP (Reg_op (Obj.magic r)))))
  
  (** val coq_POPSR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_POPSR_p =
    alt instruction_t
      (map (bits_n (length ('1'::('1'::('1'::[]))))) instruction_t
        (bitsleft (bits_n (length ('1'::('1'::('1'::[])))))
          ('0'::('0'::('0'::[])))
          (bitsleft (bits_n (length ('1'::('1'::('1'::[])))))
            ('0'::('0'::[])) (bits ('1'::('1'::('1'::[])))))) (fun x ->
        Obj.magic (POPSR ES)))
      (alt instruction_t
        (map (bits_n (length ('1'::('1'::('1'::[]))))) instruction_t
          (bitsleft (bits_n (length ('1'::('1'::('1'::[])))))
            ('0'::('0'::('0'::[])))
            (bitsleft (bits_n (length ('1'::('1'::('1'::[])))))
              ('1'::('0'::[])) (bits ('1'::('1'::('1'::[])))))) (fun x ->
          Obj.magic (POPSR SS)))
        (alt instruction_t
          (map (bits_n (length ('1'::('1'::('1'::[]))))) instruction_t
            (bitsleft (bits_n (length ('1'::('1'::('1'::[])))))
              ('0'::('0'::('0'::[])))
              (bitsleft (bits_n (length ('1'::('1'::('1'::[])))))
                ('1'::('1'::[])) (bits ('1'::('1'::('1'::[])))))) (fun x ->
            Obj.magic (POPSR DS)))
          (alt instruction_t
            (map (bits_n (length ('0'::('0'::('1'::[]))))) instruction_t
              (bitsleft (bits_n (length ('0'::('0'::('1'::[])))))
                ('0'::('0'::('0'::('0'::[]))))
                (bitsleft (bits_n (length ('0'::('0'::('1'::[])))))
                  ('1'::('1'::('1'::('1'::[]))))
                  (bitsleft (bits_n (length ('0'::('0'::('1'::[])))))
                    ('1'::('0'::[]))
                    (bitsleft (bits_n (length ('0'::('0'::('1'::[])))))
                      ('1'::('0'::('0'::[]))) (bits ('0'::('0'::('1'::[]))))))))
              (fun x -> Obj.magic (POPSR FS)))
            (map (bits_n (length ('0'::('0'::('1'::[]))))) instruction_t
              (bitsleft (bits_n (length ('0'::('0'::('1'::[])))))
                ('0'::('0'::('0'::('0'::[]))))
                (bitsleft (bits_n (length ('0'::('0'::('1'::[])))))
                  ('1'::('1'::('1'::('1'::[]))))
                  (bitsleft (bits_n (length ('0'::('0'::('1'::[])))))
                    ('1'::('0'::[]))
                    (bitsleft (bits_n (length ('0'::('0'::('1'::[])))))
                      ('1'::('0'::('1'::[]))) (bits ('0'::('0'::('1'::[]))))))))
              (fun x -> Obj.magic (POPSR GS))))))
  
  (** val coq_POPA_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_POPA_p =
    map (bits_n (length ('0'::('0'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('0'::('0'::('1'::[]))))))
        ('0'::('1'::('1'::('0'::[])))) (bits ('0'::('0'::('0'::('1'::[]))))))
      (fun x -> Obj.magic POPA)
  
  (** val coq_POPF_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_POPF_p =
    map (bits_n (length ('1'::('1'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('0'::('1'::[]))))))
        ('1'::('0'::('0'::('1'::[])))) (bits ('1'::('1'::('0'::('1'::[]))))))
      (fun x -> Obj.magic POPF)
  
  (** val coq_PUSH_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PUSH_p =
    alt instruction_t
      (map operand_t instruction_t
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
            (ext_op_modrm ('1'::('1'::('0'::[])))))) (fun x ->
        Obj.magic (PUSH (true, (Obj.magic x)))))
      (alt instruction_t
        (map register_t instruction_t
          (bitsleft register_t ('0'::('1'::('0'::('1'::[]))))
            (bitsleft register_t ('0'::[]) reg)) (fun r ->
          Obj.magic (PUSH (true, (Reg_op (Obj.magic r))))))
        (alt instruction_t
          (map byte_t instruction_t
            (bitsleft byte_t ('0'::('1'::('1'::('0'::[]))))
              (bitsleft byte_t ('1'::('0'::('1'::('0'::[])))) byte))
            (fun b ->
            Obj.magic (PUSH (false, (Imm_op
              (zero_extend8_32 (Obj.magic b)))))))
          (map word_t instruction_t
            (bitsleft word_t ('0'::('1'::('1'::('0'::[]))))
              (bitsleft word_t ('1'::('0'::('0'::('0'::[])))) word))
            (fun w -> Obj.magic (PUSH (true, (Imm_op (Obj.magic w))))))))
  
  (** val segment_reg2_p : X86_BASE_PARSER.coq_parser **)
  
  let segment_reg2_p =
    alt segment_register_t
      (map (bits_n (length ('0'::('0'::[])))) segment_register_t
        (bits ('0'::('0'::[]))) (fun x -> Obj.magic ES))
      (alt segment_register_t
        (map (bits_n (length ('0'::('1'::[])))) segment_register_t
          (bits ('0'::('1'::[]))) (fun x -> Obj.magic CS))
        (alt segment_register_t
          (map (bits_n (length ('1'::('0'::[])))) segment_register_t
            (bits ('1'::('0'::[]))) (fun x -> Obj.magic SS))
          (map (bits_n (length ('1'::('1'::[])))) segment_register_t
            (bits ('1'::('1'::[]))) (fun x -> Obj.magic DS))))
  
  (** val coq_PUSHSR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PUSHSR_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (segment_register_t,
        (bits_n (length ('1'::('1'::('0'::[]))))))) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (segment_register_t,
          (bits_n (length ('1'::('1'::('0'::[]))))))) ('0'::('0'::('0'::[])))
          (seq segment_register_t (bits_n (length ('1'::('1'::('0'::[])))))
            segment_reg2_p (bits ('1'::('1'::('0'::[])))))) (fun p ->
        Obj.magic (PUSHSR (fst (Obj.magic p)))))
      (alt instruction_t
        (map (bits_n (length ('0'::('0'::('0'::[]))))) instruction_t
          (bitsleft (bits_n (length ('0'::('0'::('0'::[])))))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (bits_n (length ('0'::('0'::('0'::[])))))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft (bits_n (length ('0'::('0'::('0'::[])))))
                ('1'::('0'::[]))
                (bitsleft (bits_n (length ('0'::('0'::('0'::[])))))
                  ('1'::('0'::('0'::[]))) (bits ('0'::('0'::('0'::[]))))))))
          (fun x -> Obj.magic (PUSHSR FS)))
        (map (bits_n (length ('0'::('0'::('0'::[]))))) instruction_t
          (bitsleft (bits_n (length ('0'::('0'::('0'::[])))))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (bits_n (length ('0'::('0'::('0'::[])))))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft (bits_n (length ('0'::('0'::('0'::[])))))
                ('1'::('0'::[]))
                (bitsleft (bits_n (length ('0'::('0'::('0'::[])))))
                  ('1'::('0'::('1'::[]))) (bits ('0'::('0'::('0'::[]))))))))
          (fun x -> Obj.magic (PUSHSR GS))))
  
  (** val coq_PUSHA_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PUSHA_p =
    map (bits_n (length ('0'::('0'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('0'::('0'::('0'::[]))))))
        ('0'::('1'::('1'::('0'::[])))) (bits ('0'::('0'::('0'::('0'::[]))))))
      (fun x -> Obj.magic PUSHA)
  
  (** val coq_PUSHF_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PUSHF_p =
    map (bits_n (length ('1'::('1'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('0'::('0'::[]))))))
        ('1'::('0'::('0'::('1'::[])))) (bits ('1'::('1'::('0'::('0'::[]))))))
      (fun x -> Obj.magic PUSHF)
  
  (** val rotate_p :
      char list -> (bool -> operand -> reg_or_immed -> instr) ->
      X86_BASE_PARSER.coq_parser **)
  
  let rotate_p extop inst =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('1'::('1'::('0'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('0'::('0'::('0'::[])))
            (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
              (ext_op_modrm2 extop)))) (fun p ->
        Obj.magic inst (fst (Obj.magic p)) (snd (Obj.magic p)) (Imm_ri
          (Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero))))))) Big.one))))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('1'::('1'::('0'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, operand_t))
              ('0'::('0'::('1'::[])))
              (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
                (ext_op_modrm2 extop)))) (fun p ->
          Obj.magic inst (fst (Obj.magic p)) (snd (Obj.magic p)) (Reg_ri ECX)))
        (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t)))) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))))
            ('1'::('1'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
              (operand_t, byte_t)))) ('0'::('0'::('0'::[])))
              (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
                (operand_t, byte_t)) anybit
                (seq operand_t byte_t (ext_op_modrm2 extop) byte))))
          (fun p ->
          let (w, r) = Obj.magic p in
          let (op, b) = r in Obj.magic inst w op (Imm_ri b))))
  
  (** val coq_RCL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_RCL_p =
    rotate_p ('0'::('1'::('0'::[]))) (fun x x0 x1 -> RCL (x, x0, x1))
  
  (** val coq_RCR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_RCR_p =
    rotate_p ('0'::('1'::('1'::[]))) (fun x x0 x1 -> RCR (x, x0, x1))
  
  (** val coq_RDMSR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_RDMSR_p =
    map (bits_n (length ('0'::('0'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
            ('0'::('0'::('1'::('1'::[]))))
            (bits ('0'::('0'::('1'::('0'::[])))))))) (fun x ->
      Obj.magic RDMSR)
  
  (** val coq_RDPMC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_RDPMC_p =
    map (bits_n (length ('0'::('0'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('0'::('1'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('0'::('0'::('1'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('0'::('0'::('1'::('1'::[]))))))
            ('0'::('0'::('1'::('1'::[]))))
            (bits ('0'::('0'::('1'::('1'::[])))))))) (fun x ->
      Obj.magic RDPMC)
  
  (** val coq_RDTSC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_RDTSC_p =
    map (bits_n (length ('0'::('0'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('0'::('0'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('0'::('0'::('0'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('0'::('0'::('0'::('1'::[]))))))
            ('0'::('0'::('1'::('1'::[]))))
            (bits ('0'::('0'::('0'::('1'::[])))))))) (fun x ->
      Obj.magic RDTSC)
  
  (** val coq_RDTSCP_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_RDTSCP_p =
    map (bits_n (length ('1'::('0'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
              ('0'::('0'::('0'::('1'::[]))))
              (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
                ('1'::('1'::('1'::('1'::[]))))
                (bits ('1'::('0'::('0'::('1'::[])))))))))) (fun x ->
      Obj.magic RDTSCP)
  
  (** val coq_RET_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_RET_p =
    alt instruction_t
      (map (bits_n (length ('0'::('0'::('1'::('1'::[])))))) instruction_t
        (bitsleft (bits_n (length ('0'::('0'::('1'::('1'::[]))))))
          ('1'::('1'::('0'::('0'::[]))))
          (bits ('0'::('0'::('1'::('1'::[])))))) (fun x ->
        Obj.magic (RET (true, None))))
      (alt instruction_t
        (map half_t instruction_t
          (bitsleft half_t ('1'::('1'::('0'::('0'::[]))))
            (bitsleft half_t ('0'::('0'::('1'::('0'::[])))) halfword))
          (fun h -> Obj.magic (RET (true, (Some (Obj.magic h))))))
        (alt instruction_t
          (map (bits_n (length ('1'::('0'::('1'::('1'::[])))))) instruction_t
            (bitsleft (bits_n (length ('1'::('0'::('1'::('1'::[]))))))
              ('1'::('1'::('0'::('0'::[]))))
              (bits ('1'::('0'::('1'::('1'::[])))))) (fun x ->
            Obj.magic (RET (false, None))))
          (map half_t instruction_t
            (bitsleft half_t ('1'::('1'::('0'::('0'::[]))))
              (bitsleft half_t ('1'::('0'::('1'::('0'::[])))) halfword))
            (fun h -> Obj.magic (RET (false, (Some (Obj.magic h))))))))
  
  (** val coq_ROL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_ROL_p =
    rotate_p ('0'::('0'::('0'::[]))) (fun x x0 x1 -> ROL (x, x0, x1))
  
  (** val coq_ROR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_ROR_p =
    rotate_p ('0'::('0'::('1'::[]))) (fun x x0 x1 -> ROR (x, x0, x1))
  
  (** val coq_RSM_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_RSM_p =
    map (bits_n (length ('1'::('0'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('1'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('1'::('0'::('1'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('1'::('0'::('1'::('0'::[]))))))
            ('1'::('0'::('1'::('0'::[]))))
            (bits ('1'::('0'::('1'::('0'::[])))))))) (fun x -> Obj.magic RSM)
  
  (** val coq_SAHF_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SAHF_p =
    map (bits_n (length ('1'::('1'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('1'::('0'::[]))))))
        ('1'::('0'::('0'::('1'::[])))) (bits ('1'::('1'::('1'::('0'::[]))))))
      (fun x -> Obj.magic SAHF)
  
  (** val coq_SAR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SAR_p =
    rotate_p ('1'::('1'::('1'::[]))) (fun x x0 x1 -> SAR (x, x0, x1))
  
  (** val coq_SCAS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SCAS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('0'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('1'::[]))) anybit))
      (fun x -> Obj.magic (SCAS (Obj.magic x)))
  
  (** val coq_SETcc_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SETcc_p =
    map (X86_BASE_PARSER.Coq_pair_t (condition_t, (X86_BASE_PARSER.Coq_pair_t
      (operand_t, operand_t)))) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            ('1'::('0'::('0'::('1'::[]))))
            (seq condition_t (X86_BASE_PARSER.Coq_pair_t (operand_t,
              operand_t)) tttn modrm)))) (fun p ->
      Obj.magic (SETcc ((fst (Obj.magic p)), (snd (snd (Obj.magic p))))))
  
  (** val coq_SGDT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SGDT_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm ('0'::('0'::('0'::[])))))))) (fun x ->
      Obj.magic (SGDT (Obj.magic x)))
  
  (** val coq_SHL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SHL_p =
    rotate_p ('1'::('0'::('0'::[]))) (fun x x0 x1 -> SHL (x, x0, x1))
  
  (** val shiftdouble_p :
      char list -> (operand -> register -> reg_or_immed ->
      X86_BASE_PARSER.result_m) -> X86_BASE_PARSER.coq_parser **)
  
  let shiftdouble_p opcode inst =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (register_t,
        (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t)))) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
          (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
            (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
              (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
              ('1'::('0'::('1'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t)))) opcode
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                  (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
                  ('0'::('0'::[]))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                    (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
                    ('1'::('1'::[]))
                    (seq register_t (X86_BASE_PARSER.Coq_pair_t (register_t,
                      byte_t)) reg (seq register_t byte_t reg byte))))))))
        (fun p ->
        let (r2, r) = Obj.magic p in
        let (r1, b) = r in inst (Reg_op r1) r2 (Imm_ri b)))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
          (register_t, operand_t)), byte_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
            (register_t, operand_t)), byte_t)) ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              ((X86_BASE_PARSER.Coq_pair_t (register_t, operand_t)), byte_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t
                ((X86_BASE_PARSER.Coq_pair_t (register_t, operand_t)),
                byte_t)) ('1'::('0'::('1'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t
                  ((X86_BASE_PARSER.Coq_pair_t (register_t, operand_t)),
                  byte_t)) opcode
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t
                    ((X86_BASE_PARSER.Coq_pair_t (register_t, operand_t)),
                    byte_t)) ('0'::('0'::[]))
                    (seq (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
                      byte_t modrm_noreg byte)))))) (fun p ->
          let (r0, b) = Obj.magic p in
          let (r, op) = r0 in inst op r (Imm_ri b)))
        (alt instruction_t
          (map (X86_BASE_PARSER.Coq_pair_t (register_t, register_t))
            instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, register_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, register_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                  register_t)) ('1'::('0'::('1'::('0'::[]))))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                    register_t)) opcode
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                      register_t)) ('0'::('1'::[]))
                      (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                        register_t)) ('1'::('1'::[]))
                        (seq register_t register_t reg reg))))))) (fun p ->
            let (r2, r1) = Obj.magic p in inst (Reg_op r1) r2 (Reg_ri ECX)))
          (map (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
            instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                  operand_t)) ('1'::('0'::('1'::('0'::[]))))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                    operand_t)) opcode
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                      operand_t)) ('0'::('1'::[])) modrm_noreg))))) (fun p ->
            let (r, op) = Obj.magic p in inst op r (Reg_ri ECX)))))
  
  (** val coq_SHLD_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SHLD_p =
    shiftdouble_p ('0'::('1'::[]))
      (Obj.magic (fun x x0 x1 -> SHLD (x, x0, x1)))
  
  (** val coq_SHR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SHR_p =
    rotate_p ('1'::('0'::('1'::[]))) (fun x x0 x1 -> SHR (x, x0, x1))
  
  (** val coq_SHRD_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SHRD_p =
    shiftdouble_p ('1'::('1'::[]))
      (Obj.magic (fun x x0 x1 -> SHRD (x, x0, x1)))
  
  (** val coq_SIDT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SIDT_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm ('0'::('0'::('1'::[])))))))) (fun x ->
      Obj.magic (SIDT (Obj.magic x)))
  
  (** val coq_SLDT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SLDT_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm ('0'::('0'::('0'::[])))))))) (fun x ->
      Obj.magic (SLDT (Obj.magic x)))
  
  (** val coq_SMSW_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SMSW_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm ('1'::('0'::('0'::[])))))))) (fun x ->
      Obj.magic (SMSW (Obj.magic x)))
  
  (** val coq_STC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_STC_p =
    map (bits_n (length ('1'::('0'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('1'::('0'::('0'::('1'::[]))))))
      (fun x -> Obj.magic STC)
  
  (** val coq_STD_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_STD_p =
    map (bits_n (length ('1'::('1'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('0'::('1'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('1'::('1'::('0'::('1'::[]))))))
      (fun x -> Obj.magic STD)
  
  (** val coq_STI_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_STI_p =
    map (bits_n (length ('1'::('0'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('1'::('1'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('1'::('0'::('1'::('1'::[]))))))
      (fun x -> Obj.magic STI)
  
  (** val coq_STOS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_STOS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('0'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('0'::('1'::[]))) anybit))
      (fun x -> Obj.magic (STOS (Obj.magic x)))
  
  (** val coq_STR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_STR_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm ('0'::('0'::('1'::[])))))))) (fun x ->
      Obj.magic (STR (Obj.magic x)))
  
  (** val coq_TEST_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_TEST_p opsize_override =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('0'::('1'::('1'::('1'::[]))))
            (seq operand_t operand_t (ext_op_modrm2 ('0'::('0'::('0'::[]))))
              (imm_op opsize_override)))) (fun p ->
        Obj.magic (TEST (true, (fst (Obj.magic p)), (snd (Obj.magic p))))))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
              ('0'::('1'::('1'::('0'::[]))))
              (seq operand_t byte_t (ext_op_modrm2 ('0'::('0'::('0'::[]))))
                byte))) (fun p ->
          Obj.magic (TEST (false, (fst (Obj.magic p)), (Imm_op
            (zero_extend8_32 (snd (Obj.magic p))))))))
        (alt instruction_t
          (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
              (operand_t, operand_t)))) ('1'::('0'::('0'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t
                (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
                (operand_t, operand_t)))) ('0'::('1'::('0'::[])))
                (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
                  (operand_t, operand_t)) anybit modrm))) (fun p ->
            let (w, r) = Obj.magic p in
            let (op1, op2) = r in Obj.magic (TEST (w, op1, op2))))
          (alt instruction_t
            (map operand_t instruction_t
              (bitsleft operand_t ('1'::('0'::('1'::('0'::[]))))
                (bitsleft operand_t ('1'::('0'::('0'::('1'::[]))))
                  (imm_op opsize_override))) (fun w ->
              Obj.magic (TEST (true, (Obj.magic w), (Reg_op EAX)))))
            (map byte_t instruction_t
              (bitsleft byte_t ('1'::('0'::('1'::('0'::[]))))
                (bitsleft byte_t ('1'::('0'::('0'::('0'::[])))) byte))
              (fun b ->
              Obj.magic (TEST (true, (Imm_op
                (zero_extend8_32 (Obj.magic b))), (Reg_op EAX))))))))
  
  (** val coq_UD2_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_UD2_p =
    map (bits_n (length ('1'::('0'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('1'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('1'::('0'::('1'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('1'::('0'::('1'::('1'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bits ('1'::('0'::('1'::('1'::[])))))))) (fun x -> Obj.magic UD2)
  
  (** val coq_VERR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_VERR_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm ('1'::('0'::('0'::[])))))))) (fun x ->
      Obj.magic (VERR (Obj.magic x)))
  
  (** val coq_VERW_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_VERW_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm ('1'::('0'::('1'::[])))))))) (fun x ->
      Obj.magic (VERW (Obj.magic x)))
  
  (** val coq_WAIT_p :
      X86_BASE_PARSER.coq_parser **)
  
(*
  let coq_WAIT_p =
    map
      (bits_n
        (length
          ('1'::('0'::('1'::('1'::(' '::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('1'::('1'::(' '::[])))))))
        ('1'::('0'::('0'::('1'::[]))))
        (bits
          ('1'::('0'::('1'::('1'::(' '::[])))))))
      (fun x ->
      Obj.magic
        WAIT)
*)
  
  (** val coq_WBINVD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_WBINVD_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('0'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('0'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('1'::('0'::('0'::('1'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bits
              ('1'::('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        WBINVD)
  
  (** val coq_WRMSR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_WRMSR_p =
    map
      (bits_n
        (length
          ('0'::('0'::('0'::('0'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('0'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('0'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('0'::('0'::('0'::('0'::[]))))))
            ('0'::('0'::('1'::('1'::[]))))
            (bits
              ('0'::('0'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        WRMSR)
  
  (** val coq_XADD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_XADD_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t
      (operand_t,
      operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            ('1'::('1'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))))
              ('0'::('0'::('0'::[])))
              (seq
                X86_BASE_PARSER.Coq_char_t
                (X86_BASE_PARSER.Coq_pair_t
                (operand_t,
                operand_t))
                anybit
                modrm)))))
      (fun p ->
      let (w,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (XADD
        (w,
        op1,
        op2)))
  
  (** val coq_XCHG_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_XCHG_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))))
          ('1'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            ('0'::('1'::('1'::[])))
            (seq
              X86_BASE_PARSER.Coq_char_t
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))
              anybit
              modrm)))
        (fun p ->
        let (w,
             r) =
          Obj.magic
            p
        in
        let (op1,
             op2) =
          r
        in
        Obj.magic
          (XCHG
          (w,
          op1,
          op2))))
      (map
        register_t
        instruction_t
        (bitsleft
          register_t
          ('1'::('0'::('0'::('1'::[]))))
          (bitsleft
            register_t
            ('0'::[])
            reg))
        (fun r ->
        Obj.magic
          (XCHG
          (true,
          (Reg_op
          EAX),
          (Reg_op
          (Obj.magic
            r))))))
  
  (** val coq_XLAT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_XLAT_p =
    map
      (bits_n
        (length
          ('0'::('1'::('1'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('1'::('1'::[]))))))
        ('1'::('1'::('0'::('1'::[]))))
        (bits
          ('0'::('1'::('1'::('1'::[]))))))
      (fun x ->
      Obj.magic
        XLAT)
  
  (** val instr_parsers_opsize_pre :
      X86_BASE_PARSER.coq_parser
      list **)
  
  let instr_parsers_opsize_pre =
    (coq_ADC_p
      true) :: ((coq_ADD_p
                  true) :: ((coq_AND_p
                              true) :: ((coq_CMP_p
                                          true) :: ((coq_OR_p
                                                      true) :: ((coq_SBB_p
                                                                  true) :: (
      (coq_SUB_p
        true) :: (coq_SHL_p :: (coq_SHLD_p :: (coq_SHR_p :: (coq_SAR_p :: (coq_SHRD_p :: (
      (coq_XOR_p
        true) :: ((coq_IMUL_p
                    true) :: ((coq_MOV_p
                                true) :: (coq_MOVSX_p :: (coq_MOVZX_p :: (coq_NEG_p :: (coq_NOT_p :: (coq_DIV_p :: (coq_IDIV_p :: (
      (coq_TEST_p
        true) :: (coq_CDQ_p :: (coq_CWDE_p :: (coq_MUL_p :: (coq_XCHG_p :: [])))))))))))))))))))))))))
  
  let op_override_p =
    map
      (bits_n
        (length
          ('0'::('1'::('1'::('0'::[]))))))
      bool_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('1'::('0'::[]))))))
        ('0'::('1'::('1'::('0'::[]))))
        (bits
          ('0'::('1'::('1'::('0'::[]))))))
      (fun x ->
      Obj.magic
        true)
  
  
