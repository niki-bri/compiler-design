open Assert
open X86
open Simulator
open Asm

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)


let provided_tests : suite = [
  Test ("Debug", [
    ("add_overflow_wraps_to_zero_sets_ZF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit 0xFFFFFFFFFFFFFFFFL); ~%Rax]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Addq, [~$1; ~%Rax]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        (* Execute both instructions *)
        for _i = 1 to 2 do step m done;
        (* Expect RAX = 0, ZF = true, SF = false, OF = false *)
        if m.regs.(rind Rax) = 0L && m.flags.fz && (not m.flags.fs) && (not m.flags.fo)
        then () else failwith "Expected RAX=0, ZF=true, SF=false, OF=false"));

    ("neg_min_int_sets_OF_and_SF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Negq, [~%Rax]);                             InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        (* Expect RAX = Int64.min_int, OF = true, SF = true, ZF = false *)
        if m.regs.(rind Rax) = Int64.min_int && m.flags.fo && m.flags.fs && (not m.flags.fz)
        then () else failwith "Expected RAX=min_int, OF=true, SF=true, ZF=false"))
    ; ("intentional_failure_for_debug", assert_fail)

    (* Additional edge-case tests *)
    ; ("xor_zero_sets_ZF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$5; ~%Rax]);              InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Xorq, [~%Rax; ~%Rax]);            InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = 0L && m.flags.fz && (not m.flags.fs) && (not m.flags.fo)
        then () else failwith "Expected XOR zero: RAX=0, ZF=true, SF=false, OF=false"))

    ; ("neg_zero_sets_ZF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$0; ~%Rax]);              InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Negq, [~%Rax]);                   InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = 0L && m.flags.fz && (not m.flags.fs) && (not m.flags.fo)
        then () else failwith "Expected NEG 0: RAX=0, ZF=true, SF=false, OF=false"))

    ; ("shr_count_zero_preserves_flags",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Shrq, [~$0; ~%Rax]);              InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        (* Seed nontrivial flags, ensure SHR by 0 preserves them *)
        let original = { fo = true; fs = false; fz = true } in
        let m = { m with flags = original } in
        step m;
        if m.flags = original then () else failwith "Expected SHR count 0 to preserve flags"))

    ; ("imul_zero_sets_ZF_and_clears_SF_OF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$123; ~%Rax]);            InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Imulq, [~$0; ~%Rax]);              InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = 0L && m.flags.fz && (not m.flags.fs) && (not m.flags.fo)
        then () else failwith "Expected IMUL by 0: RAX=0, ZF=true, SF=false, OF=false"))

    ; ("cmp_equal_sets_ZF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$42; ~%Rax]);             InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Cmpq, [~$42; ~%Rax]);             InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.flags.fz && (not m.flags.fs) && (not m.flags.fo)
        then () else failwith "Expected CMP equal: ZF=true, SF=false, OF=false"))

    ; ("add_pos_overflow_sets_OF_SF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit 0x7FFFFFFFFFFFFFFFL); ~%Rax]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Addq, [~$1; ~%Rax]);                            InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = Int64.min_int && m.flags.fo && m.flags.fs && (not m.flags.fz)
        then () else failwith "Expected add overflow: RAX=min_int, OF=true, SF=true, ZF=false"))

    ; ("sub_pos_minus_neg_overflow_sets_OF_SF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit 0x7FFFFFFFFFFFFFFFL); ~%Rax]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Subq, [~$(-1); ~%Rax]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = Int64.min_int && m.flags.fo && m.flags.fs && (not m.flags.fz)
        then () else failwith "Expected sub overflow: RAX=min_int, OF=true, SF=true, ZF=false"))

    ; ("cmp_minus1_vs_zero_sets_SF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$(-1); ~%Rax]);          InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Cmpq, [~$0; ~%Rax]);             InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if (not m.flags.fz) && m.flags.fs
        then () else failwith "Expected CMP -1,0: SF=true, ZF=false"))

    ; ("sar63_keeps_minus_one",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$(-1); ~%Rax]);          InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Sarq, [~$63; ~%Rax]);            InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = -1L && (not m.flags.fz) && m.flags.fs
        then () else failwith "Expected SAR 63 of -1: RAX=-1, SF=true, ZF=false"))

    ; ("shr63_from_one_sets_ZF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$1; ~%Rax]);             InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Shrq, [~$63; ~%Rax]);            InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = 0L && m.flags.fz && (not m.flags.fs)
        then () else failwith "Expected SHR 63 of 1: RAX=0, ZF=true, SF=false"))

    ; ("inc_from_neg1_sets_ZF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$(-1); ~%Rax]);          InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Incq, [~%Rax]);                  InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = 0L && m.flags.fz && (not m.flags.fs)
        then () else failwith "Expected INC of -1: RAX=0, ZF=true, SF=false"))

    ; ("dec_from_zero_sets_SF",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$0; ~%Rax]);             InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Decq, [~%Rax]);                  InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = -1L && (not m.flags.fz) && m.flags.fs
        then () else failwith "Expected DEC of 0: RAX=-1, SF=true, ZF=false"))

    (* New batch per request: segfault, shift-by-64 semantics, jump Gt taken/not-taken, setcc to memory *)
    ; ("mov_from_null_segfault",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Ind1 (Lit 0x0L); ~%Rax]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        try step m; failwith "Expected X86lite_segfault"
        with Simulator.X86lite_segfault -> ()))

    ; ("shl_64_masks_to_zero_count",
      (fun () ->
        (* Since counts are masked with 63, 64 behaves like 0. Our simulator recomputes flags from the result. *)
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [~$0; ~%Rax]);             InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Shlq, [~$64; ~%Rax]);            InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        for _i = 1 to 2 do step m done;
        if m.regs.(rind Rax) = 0L && m.flags.fz && (not m.flags.fs) && (not m.flags.fo)
        then () else failwith "Expected SHL 64 of 0: RAX=0, ZF=true, SF=false, OF=false"))

    ; ("j_gt_taken_sets_rip",
      (fun () ->
        let target = Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L) in
        let m = Gradedtests.test_machine
          [ InsB0 (J Gt, [Imm (Lit target)]);      InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        step m;
        if m.regs.(rind Rip) = target then () else failwith "Expected JG taken to target"))

    ; ("j_gt_not_taken_falls_through",
      (fun () ->
        let next = Int64.add Simulator.mem_bot Simulator.ins_size in
        let m = Gradedtests.test_machine
          [ InsB0 (J Gt, [Imm (Lit (Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L)))]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = true } } in
        step m;
        if m.regs.(rind Rip) = next then () else failwith "Expected JG not taken to fall-through"))

    ; ("set_eq_mem_true_writes_1",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Eq, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = true } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 254L in
        if v = expected then () else failwith "Expected setcc true to write ...FF01"))

    ; ("set_eq_mem_false_writes_0",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Eq, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 255L in
        if v = expected then () else failwith "Expected setcc false to write ...FF00"))

    (* Jump tests for all condition codes (taken and not-taken) *)
    ; ("j_eq_taken_sets_rip",
      (fun () ->
        let target = Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L) in
        let m = Gradedtests.test_machine
          [ InsB0 (J Eq, [Imm (Lit target)]);       InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = true; fz = true } } in
        step m; if m.regs.(rind Rip) = target then () else failwith "Expected JE taken"))
    ; ("j_eq_not_taken_falls_through",
      (fun () ->
        let next = Int64.add Simulator.mem_bot Simulator.ins_size in
        let m = Gradedtests.test_machine
          [ InsB0 (J Eq, [Imm (Lit (Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L)))]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        step m; if m.regs.(rind Rip) = next then () else failwith "Expected JE not taken"))

    ; ("j_neq_taken_sets_rip",
      (fun () ->
        let target = Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L) in
        let m = Gradedtests.test_machine
          [ InsB0 (J Neq, [Imm (Lit target)]);      InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        step m; if m.regs.(rind Rip) = target then () else failwith "Expected JNE taken"))
    ; ("j_neq_not_taken_falls_through",
      (fun () ->
        let next = Int64.add Simulator.mem_bot Simulator.ins_size in
        let m = Gradedtests.test_machine
          [ InsB0 (J Neq, [Imm (Lit (Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L)))]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = true } } in
        step m; if m.regs.(rind Rip) = next then () else failwith "Expected JNE not taken"))

    ; ("j_ge_taken_sets_rip",
      (fun () ->
        let target = Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L) in
        let m = Gradedtests.test_machine
          [ InsB0 (J Ge, [Imm (Lit target)]);       InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        step m; if m.regs.(rind Rip) = target then () else failwith "Expected JGE taken"))
    ; ("j_ge_not_taken_falls_through",
      (fun () ->
        let next = Int64.add Simulator.mem_bot Simulator.ins_size in
        let m = Gradedtests.test_machine
          [ InsB0 (J Ge, [Imm (Lit (Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L)))]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = false } } in
        step m; if m.regs.(rind Rip) = next then () else failwith "Expected JGE not taken"))

    ; ("j_lt_taken_sets_rip",
      (fun () ->
        let target = Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L) in
        let m = Gradedtests.test_machine
          [ InsB0 (J Lt, [Imm (Lit target)]);       InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = false } } in
        step m; if m.regs.(rind Rip) = target then () else failwith "Expected JL taken"))
    ; ("j_lt_not_taken_falls_through",
      (fun () ->
        let next = Int64.add Simulator.mem_bot Simulator.ins_size in
        let m = Gradedtests.test_machine
          [ InsB0 (J Lt, [Imm (Lit (Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L)))]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        step m; if m.regs.(rind Rip) = next then () else failwith "Expected JL not taken"))

    ; ("j_le_taken_sets_rip",
      (fun () ->
        let target = Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L) in
        let m = Gradedtests.test_machine
          [ InsB0 (J Le, [Imm (Lit target)]);       InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = true } } in
        step m; if m.regs.(rind Rip) = target then () else failwith "Expected JLE taken"))
    ; ("j_le_not_taken_falls_through",
      (fun () ->
        let next = Int64.add Simulator.mem_bot Simulator.ins_size in
        let m = Gradedtests.test_machine
          [ InsB0 (J Le, [Imm (Lit (Int64.add Simulator.mem_bot (Int64.mul Simulator.ins_size 2L)))]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        step m; if m.regs.(rind Rip) = next then () else failwith "Expected JLE not taken"))

    (* setcc tests to memory for all cnds, both outcomes *)
    ; ("set_neq_mem_true_writes_1",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Neq, [loc]);                        InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 254L in
        if v = expected then () else failwith "Expected setne true to write ...FF01"))
    ; ("set_neq_mem_false_writes_0",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Neq, [loc]);                        InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = true } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 255L in
        if v = expected then () else failwith "Expected setne false to write ...FF00"))

    ; ("set_gt_mem_true_writes_1",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Gt, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 254L in
        if v = expected then () else failwith "Expected setg true to write ...FF01"))
    ; ("set_gt_mem_false_writes_0",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Gt, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = true } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 255L in
        if v = expected then () else failwith "Expected setg false to write ...FF00"))

    ; ("set_ge_mem_true_writes_1",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Ge, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 254L in
        if v = expected then () else failwith "Expected setge true to write ...FF01"))
    ; ("set_ge_mem_false_writes_0",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Ge, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 255L in
        if v = expected then () else failwith "Expected setge false to write ...FF00"))

    ; ("set_lt_mem_true_writes_1",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Lt, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 254L in
        if v = expected then () else failwith "Expected setl true to write ...FF01"))
    ; ("set_lt_mem_false_writes_0",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Lt, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 255L in
        if v = expected then () else failwith "Expected setl false to write ...FF00"))

    ; ("set_le_mem_true_writes_1",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Le, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = true } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 254L in
        if v = expected then () else failwith "Expected setle true to write ...FF01"))
    ; ("set_le_mem_false_writes_0",
      (fun () ->
        let loc = Gradedtests.stack_offset 0L in
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); loc]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Le, [loc]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let v = Simulator.int64_of_sbytes (Gradedtests.sbyte_list m.mem (Simulator.mem_size - 8)) in
        let expected = Int64.sub Int64.max_int 255L in
        if v = expected then () else failwith "Expected setle false to write ...FF00"))

    (* setcc-to-register tests for all condition codes (preserve upper bytes) *)
    ; ("set_eq_reg_true_lowbyte_1",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Eq, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = true; fz = true } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 254L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF01"))
    ; ("set_eq_reg_false_lowbyte_0",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Eq, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 255L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF00"))

    ; ("set_neq_reg_true_lowbyte_1",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Neq, [~%Rcx]);                        InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 254L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF01"))
    ; ("set_neq_reg_false_lowbyte_0",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Neq, [~%Rcx]);                        InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = true } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 255L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF00"))

    ; ("set_gt_reg_true_lowbyte_1",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Gt, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 254L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF01"))
    ; ("set_gt_reg_false_lowbyte_0",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Gt, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = true } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 255L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF00"))

    ; ("set_ge_reg_true_lowbyte_1",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Ge, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 254L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF01"))
    ; ("set_ge_reg_false_lowbyte_0",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Ge, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 255L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF00"))

    ; ("set_lt_reg_true_lowbyte_1",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Lt, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 254L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF01"))
    ; ("set_lt_reg_false_lowbyte_0",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Lt, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 255L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF00"))

    ; ("set_le_reg_true_lowbyte_1",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Le, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = true; fs = false; fz = true } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 254L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF01"))
    ; ("set_le_reg_false_lowbyte_0",
      (fun () ->
        let m = Gradedtests.test_machine
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx]); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ; InsB0 (Set Le, [~%Rcx]);                         InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag
          ] in
        let m = { m with flags = { fo = false; fs = false; fz = false } } in
        for _i = 1 to 2 do step m done;
        let expected = Int64.sub Int64.max_int 255L in
        if m.regs.(rind Rcx) = expected then () else failwith "Expected reg ...FF00"))
  ]);

] 
