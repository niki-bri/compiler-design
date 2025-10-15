(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics
*)

open X86
(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd (f:flags) : cnd -> bool = function
  | Eq -> f.fz
  | Neq -> not f.fz
  | Gt -> not f.fz && (f.fo = f.fs)
  | Ge -> f.fo = f.fs
  | Lt -> f.fo <> f.fs
  | Le -> f.fz || (f.fo <> f.fs)

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if Int64.compare addr mem_bot < 0 || Int64.compare addr mem_top >= 0 then
    None
  else
    Some (Int64.to_int (Int64.sub addr mem_bot))

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
(* --- fetch -------------------------------------------------------------- *)
let fetch_ins (m:mach) : ins =
  let rip = m.regs.(rind Rip) in
  match map_addr rip with
  | None -> raise X86lite_segfault
  | Some i ->
    (match m.mem.(i) with
     | InsB0 ins -> ins
     | _ -> invalid_arg "fetch: RIP not at instruction start")

(* --- immediates --------------------------------------------------------- *)
let eval_imm : imm -> int64 = function
  | Lit i -> i
  | Lbl _ -> invalid_arg "runtime label: assembler should have resolved labels"

(* --- effective address for indirect operands ---------------------------- *)
let eff_addr (m:mach) (op:operand) : quad =
  match op with
  | Ind1 i        -> eval_imm i
  | Ind2 r        -> m.regs.(rind r)
  | Ind3 (i,  r)  -> Int64.add (eval_imm i) m.regs.(rind r)
  | _ -> invalid_arg "eff_addr: not an addressing operand"

(* --- 8-byte memory I/O --------------------------------------------------- *)
let read_quad (m:mach) (addr:quad) : int64 =
  match map_addr addr with
  | None -> raise X86lite_segfault
  | Some i ->
      if i + 7 >= Array.length m.mem then raise X86lite_segfault;
      int64_of_sbytes
        [ m.mem.(i); m.mem.(i+1); m.mem.(i+2); m.mem.(i+3)
        ; m.mem.(i+4); m.mem.(i+5); m.mem.(i+6); m.mem.(i+7) ]

let write_quad (m:mach) (addr:quad) (v:int64) : unit =
  match map_addr addr with
  | None -> raise X86lite_segfault
  | Some i ->
      if i + 7 >= Array.length m.mem then raise X86lite_segfault;
      let bs = sbytes_of_int64 v in
      List.iteri (fun k b -> m.mem.(i + k) <- b) bs

(* --- operand read/write -------------------------------------------------- *)
let read_op (m:mach) (op:operand) : int64 =
  match op with
  | Imm i   -> eval_imm i
  | Reg r   -> m.regs.(rind r)
  | Ind1 _ | Ind2 _ | Ind3 _ ->
      read_quad m (eff_addr m op)

let write_op (m:mach) (op:operand) (v:int64) : unit =
  match op with
  | Reg r -> m.regs.(rind r) <- v
  | Ind1 _ | Ind2 _ | Ind3 _ ->
      write_quad m (eff_addr m op) v
  | Imm _ -> invalid_arg "write_op: cannot write to an immediate"

  let step (m:mach) : unit =
  let open Int64_overflow in
  let (op, args) = fetch_ins m in

 let next_rip = Int64.add m.regs.(rind Rip) ins_size in

  match op with
  | Movq -> 
    (match args with
       | [src; dst] ->
           let v = read_op m src in
           write_op m dst v;
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "movq: wrong number of operands")
  | Pushq -> 
    (match args with
    | [src] ->
        let v = read_op m src in
        (* decrement stack pointer by 8 bytes *)
        let new_rsp = Int64.sub (m.regs.(rind Rsp)) 8L in
        m.regs.(rind Rsp) <- new_rsp;
        (* store value on top of stack *)
        write_quad m new_rsp v;
        (* advance instruction pointer *)
        m.regs.(rind Rip) <- next_rip
    | _ -> invalid_arg "pushq: wrong number of operands")
  | Popq -> 
    (match args with
    | [dst] ->
        let rsp = m.regs.(rind Rsp) in
        (* read 8 bytes from the stack top *)
        let v = read_quad m rsp in
        (* increment rsp to pop the value *)
        m.regs.(rind Rsp) <- Int64.add rsp 8L;
        (* write the popped value into destination *)
        write_op m dst v;
        (* advance instruction pointer *)
        m.regs.(rind Rip) <- next_rip
    | _ -> invalid_arg "popq: wrong number of operands")
  | Leaq -> 
    (match args with
       | [addr; dst] ->
           (* compute effective address; do NOT read memory *)
           let ea = eff_addr m addr in
           write_op m dst ea;
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "leaq: wrong number of operands")
  | Incq ->
    (match args with
     | [dst] ->
         let v = read_op m dst in
         let { value = result; overflow = ofl } = Int64_overflow.succ v in
         write_op m dst result;
         m.flags.fo <- ofl;
         m.flags.fz <- (result = 0L);
         m.flags.fs <- (result < 0L);
         m.regs.(rind Rip) <- next_rip
     | _ -> invalid_arg "incq: wrong number of operands")
  | Decq -> 
    (match args with
       | [dst] ->
           let v = read_op m dst in
           let { value = r; overflow = ofl } = Int64_overflow.pred v in
           write_op m dst r;
           m.flags.fo <- ofl; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "decq: wrong number of operands")
  | Negq -> 
    (match args with
    | [dst] ->
        let v = read_op m dst in
        let { value = r; overflow = ofl } = Int64_overflow.neg v in
        write_op m dst r;
        m.flags.fo <- ofl; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
        m.regs.(rind Rip) <- next_rip
    | _ -> invalid_arg "negq: wrong number of operands")
  | Notq -> 
    (match args with
    | [dst] ->
        let v = read_op m dst in
        let r = Int64.lognot v in
        write_op m dst r;
        (* x86 NOT doesn't affect flags; leave them unchanged *)
        m.regs.(rind Rip) <- next_rip
    | _ -> invalid_arg "notq: wrong number of operands")
  | Addq -> 
    (match args with
    | [src; dst] ->
        let x = read_op m dst in
        let y = read_op m src in
        let { value = r; overflow = ofl } = Int64_overflow.add x y in
        write_op m dst r;
        m.flags.fo <- ofl; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
        m.regs.(rind Rip) <- next_rip
    | _ -> invalid_arg "addq: wrong number of operands")
  | Subq ->
      (match args with
       | [src; dst] ->
           let x = read_op m dst in
           let y = read_op m src in
           let { value = r; overflow = ofl } = Int64_overflow.sub x y in
           write_op m dst r;
           m.flags.fo <- ofl; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "subq: wrong number of operands")
  | Imulq ->
      (match args with
       | [src; dst] ->
           let x = read_op m dst in
           let y = read_op m src in
           let { value = r; overflow = ofl } = Int64_overflow.mul x y in
           write_op m dst r;
           m.flags.fo <- ofl; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "imulq: wrong number of operands")
  | Xorq ->
      (match args with
       | [src; dst] ->
           let r = Int64.logxor (read_op m dst) (read_op m src) in
           write_op m dst r;
           m.flags.fo <- false; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "xorq: wrong number of operands")
  | Orq ->
      (match args with
       | [src; dst] ->
           let r = Int64.logor (read_op m dst) (read_op m src) in
           write_op m dst r;
           m.flags.fo <- false; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "orq: wrong number of operands")
  | Andq ->
      (match args with
       | [src; dst] ->
           let r = Int64.logand (read_op m dst) (read_op m src) in
           write_op m dst r;
           m.flags.fo <- false; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "andq: wrong number of operands")
  | Shlq ->
      (match args with
       | [cnt; dst] ->
           let x = read_op m dst in
           let c = Int64.(to_int (logand (read_op m cnt) 63L)) in
           let r = Int64.shift_left x c in
           write_op m dst r;
           m.flags.fo <- false; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "shlq: wrong number of operands")
  | Sarq ->
      (match args with
       | [cnt; dst] ->
           let x = read_op m dst in
           let c = Int64.(to_int (logand (read_op m cnt) 63L)) in
           let r = Int64.shift_right x c in
           write_op m dst r;
           m.flags.fo <- false; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "sarq: wrong number of operands")
  | Shrq ->
      (match args with
       | [cnt; dst] ->
           let x = read_op m dst in
           let c = Int64.(to_int (logand (read_op m cnt) 63L)) in
           let r = Int64.shift_right_logical x c in
           write_op m dst r;
           m.flags.fo <- false; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "shrq: wrong number of operands")
  | Jmp ->
      (match args with
       | [tgt] ->
           let addr = read_op m tgt in
           m.regs.(rind Rip) <- addr
       | _ -> invalid_arg "jmp: wrong number of operands")
  | J c ->
      (match args with
       | [tgt] ->
           if interp_cnd m.flags c
           then m.regs.(rind Rip) <- read_op m tgt
           else m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "j<cnd>: wrong number of operands")
  | Cmpq ->
      (match args with
       | [src; dst] ->
           let x = read_op m dst in
           let y = read_op m src in
           let { value = r; overflow = ofl } = Int64_overflow.sub x y in
           m.flags.fo <- ofl; m.flags.fz <- (r = 0L); m.flags.fs <- (r < 0L);
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "cmpq: wrong number of operands")
  | Set c ->
      (match args with
       | [dst] ->
           let bit = if interp_cnd m.flags c then 1 else 0 in
           (match dst with
            | Reg r ->
                let old = m.regs.(rind r) in
                let masked = Int64.logand old 0xffffffffffffff00L in
                let newv = Int64.logor masked (Int64.of_int bit) in
                m.regs.(rind r) <- newv
            | Imm _ -> invalid_arg "set<cnd>: cannot write to immediate"
            | (Ind1 _ | Ind2 _ | Ind3 _) as op ->
                let addr = eff_addr m op in
                (match map_addr addr with
                 | None -> raise X86lite_segfault
                 | Some i ->
                     m.mem.(i) <- Byte (Char.chr bit)));
           (* FLAGS: setcc doesn't modify flags *)
           m.regs.(rind Rip) <- next_rip
       | _ -> invalid_arg "set<cnd>: wrong number of operands")
  | Callq ->
      (match args with
       | [tgt] ->
           let ret = Int64.add m.regs.(rind Rip) ins_size in
           let rsp' = Int64.sub (m.regs.(rind Rsp)) 8L in
           m.regs.(rind Rsp) <- rsp';
           write_quad m rsp' ret;
           m.regs.(rind Rip) <- read_op m tgt
       | _ -> invalid_arg "callq: wrong number of operands")
  | Retq ->
      (match args with
       | [] ->
           let rsp = m.regs.(rind Rsp) in
           let addr = read_quad m rsp in
           m.regs.(rind Rsp) <- Int64.add rsp 8L;
           m.regs.(rind Rip) <- addr
       | _ -> invalid_arg "retq: unexpected operands")
  
  


(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let assemble (_p:prog) : exec =
failwith "assemble unimplemented"

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry=_; text_pos=_; data_pos=_; text_seg=_; data_seg=_} : mach = 
failwith "load unimplemented"



