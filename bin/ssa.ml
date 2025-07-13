(* file: ssa.ml *)

(*
  This file defines a custom Static Single Assignment (SSA) based
  Intermediate Representation (IR) and an associated Dead Code
  Elimination (DCE) optimization pass.

  This IR is designed to be independent of LLVM.
*)

open Ast (* For reusing the binop type *)

(*
  I. SSA IR Definition
  --------------------
  This IR is structured around functions, basic blocks, and instructions.
  Every instruction that produces a value assigns it to a unique virtual
  register.
*)
module Ssa = struct

  (* === Identifiers === *)

  (* A unique identifier for a virtual register. *)
  type reg = R of int

  (* A unique identifier for a basic block. *)
  type bbid = L of int


  (* === Operands === *)

  (* Operands are the inputs to instructions. They can be a constant,
     the value from a register, or a global name (like a function). *)
  type operand =
    | O_Cst of int
    | O_Reg of reg
    | O_Global of string


  (* === Instructions and Terminators === *)

  (* A 'definition' represents the right-hand side of an assignment.
     It's the core operation that computes a value. *)
  type definition =
    (* Binary operation: e.g., add op1, op2 *)
    | D_BinOp of binop * operand * operand
    (* Function call: e.g., call @func(op1, op2) *)
    | D_Call of string * operand list
    (* Phi node to merge values from different predecessor blocks.
       e.g., phi [op1, from_block1], [op2, from_block2] *)
    | D_Phi of (operand * bbid) list
    (* Memory allocation on the stack, produces a pointer. *)
    | D_Alloca of string (* The type being allocated, e.g., "int", "int*" *)
    (* Load a value from a memory address (which is an operand). *)
    | D_Load of operand
    (* A 'Store' is not a definition because it doesn't produce a value.
       It's a side-effecting instruction handled separately. *)

  (* An 'instruction' assigns the result of a definition to a register.
     This is the fundamental SSA form: reg = operation *)
  type instruction = {
    reg: reg;
    def: definition;
  }
 
  (* Side-effecting instructions that do not produce a register value. *)
  type side_effect_instr =
    (* Store a value into a memory address. *)
    | S_Store of operand * operand (* S_Store address, value *)
 
  (* A basic block operation can be a value-defining instruction or
     a side-effecting one. This preserves their original order. *)
  type operation =
    | I_Instr of instruction
    | I_Side_Effect of side_effect_instr
 
  (* A 'terminator' is the last instruction in a basic block. It
     controls the flow of execution. *)
  type terminator =
    (* Return from the function, optionally with a value. *)
    | T_Ret of operand
    (* Unconditional branch to another basic block. *)
    | T_Br of bbid
    (* Conditional branch. *)
    | T_CBr of operand * bbid * bbid (* cond, true_label, false_label *)


  (* === Structural Components === *)

  (* A basic block contains a list of instructions and one terminator. *)
  type basic_block = {
    id: bbid;
    ops: operation list;
    term: terminator;
  }

  (* A function definition. *)
  type func_def = {
    name: string;
    params: reg list; (* Parameters are passed in registers. *)
    blocks: basic_block list;
    reg_types: (reg, string) Hashtbl.t;
  }

  (* A program is a list of function definitions. *)
  type program = func_def list

end


(*
  II. Dead Code Elimination (DCE) Pass
  ------------------------------------
  This pass removes instructions whose results are never used.
*)
module Dce = struct
  open Ssa

  (* Helper to extract all registers used by an operand. *)
  let used_regs_from_operand op =
    match op with
    | O_Reg r -> [r]
    | O_Cst _ | O_Global _ -> []

  (* Helper to extract all registers used by a list of operands. *)
  let used_regs_from_operands ops =
    List.concat_map used_regs_from_operand ops

  (* Traverses a definition to find all registers it uses. *)
  let get_used_regs_from_def def =
    match def with
    | D_BinOp (_, op1, op2) -> used_regs_from_operands [op1; op2]
    | D_Call (_, args) -> used_regs_from_operands args
    | D_Phi phis ->
        let ops = List.map (fun (op, _) -> op) phis in
        used_regs_from_operands ops
    | D_Alloca _ -> []
    | D_Load addr_op -> used_regs_from_operand addr_op

  (* Traverses a side-effecting instruction to find its used registers. *)
  let get_used_regs_from_side_effect sei =
    match sei with
    | S_Store (addr, value) -> used_regs_from_operands [addr; value]

  (* Traverses a terminator to find all registers it uses. *)
  let get_used_regs_from_term term =
    match term with
    | T_Ret op -> used_regs_from_operand op
    | T_CBr (cond, _, _) -> used_regs_from_operand cond
    | T_Br _ -> []

  (*
    The main DCE algorithm. It works by identifying all "live" code
    and removing everything else. An instruction is live if it has an
    observable side effect or if its result is used by another live
    instruction.

    The algorithm works backwards from the "roots" of liveness:
    1. Roots are instructions that are inherently live: returns, branches,
       stores, and calls (which might have side effects).
    2. We build a worklist of registers that are required by these root
       instructions.
    3. We iteratively process the worklist. For each required register,
       we find the instruction that defines it, mark it as live, and add
       all registers *it* uses to the worklist.
    4. This continues until the worklist is empty.
    5. Finally, we reconstruct the function, keeping only the live instructions.
  *)
  let run_on_function (f: func_def) : func_def =
    (* A map from a register to the instruction that defines it. *)
    let reg_def_map = Hashtbl.create 64 in
    List.iter (fun (bb: basic_block) ->
      List.iter (function
        | I_Instr instr -> Hashtbl.add reg_def_map instr.reg instr
        | I_Side_Effect _ -> ()
      ) bb.ops
    ) f.blocks;

    (* Find alloca'd pointers that are actually used. A pointer is "used"
       if it is loaded from or passed to a function (which might load from it).
       A store does not count as a "use" for this purpose. This helps
       identify stores to dead local variables. *)
    let used_pointers = Hashtbl.create 16 in
    let is_alloca_reg r =
      match Hashtbl.find_opt reg_def_map r with
      | Some { def = D_Alloca _; _ } -> true
      | _ -> false
    in
    List.iter (fun bb ->
        List.iter (function
            | I_Instr { def = D_Load (O_Reg p); _ } when is_alloca_reg p ->
                Hashtbl.replace used_pointers p ()
            | I_Instr { def = D_Call (_, args); _ } ->
                List.iter (fun arg -> match arg with O_Reg p when is_alloca_reg p -> Hashtbl.replace used_pointers p () | _ -> ()) args
            | _ -> ()
        ) bb.ops
    ) f.blocks;

    (* A set to store the registers that are defined by live instructions.
       We use a Hashtbl for its efficient lookups. *)
    let live_regs = Hashtbl.create 64 in
    let worklist = ref [] in

    (* Helper to add a register to the worklist if it's not already there
       or marked as live. This avoids redundant work. *)
    let add_to_worklist r =
      if not (Hashtbl.mem live_regs r) && not (List.mem r !worklist) then
        worklist := r :: !worklist
    in

    (* 1. Initialize worklist with the roots of liveness. *)
    List.iter (fun bb ->
      (* Registers used by terminators are live. *)
      List.iter add_to_worklist (get_used_regs_from_term bb.term);

      (* Side-effecting operations (stores, calls) are roots. *)
      List.iter (function
        | I_Side_Effect (S_Store (addr, _) as sei) ->
            (* A store is only a root of liveness if it's to a pointer
               that is actually used, or it's not a known local alloca. *)
            let is_live_store = match addr with
              | O_Reg p when is_alloca_reg p -> Hashtbl.mem used_pointers p
              | _ -> true (* Store to a param pointer, global, etc. -> consider live *)
            in
            if is_live_store then
              List.iter add_to_worklist (get_used_regs_from_side_effect sei)
        | I_Instr instr ->
            (* All calls are considered live due to potential side effects.
         Therefore, the registers they use are live, and if they
         produce a result, that result *might* be live if used elsewhere.
         For simplicity and correctness, we treat all call instructions
         themselves as live roots. *)
            (match instr.def with
            | D_Call _ ->
              (* The result register of a live instruction is live. *)
              Hashtbl.replace live_regs instr.reg ();
              (* And all its argument registers need to be processed. *)
              List.iter add_to_worklist (get_used_regs_from_def instr.def)
            | _ -> ())
      ) bb.ops
    ) f.blocks;

    (* 2. Iteratively find all live instructions. *)
    while !worklist <> [] do
      let reg_to_process = List.hd !worklist in
      worklist := List.tl !worklist;

      if not (Hashtbl.mem live_regs reg_to_process) then begin
        (* Mark this register as live, since it's used by a live instruction. *)
        Hashtbl.add live_regs reg_to_process ();

        (* Find the instruction that defines this register. *)
        match Hashtbl.find_opt reg_def_map reg_to_process with
        | Some defining_instr ->
            (* The instruction is now known to be live. Add all registers
               it depends on to the worklist. *)
            let used_regs = get_used_regs_from_def defining_instr.def in
            List.iter add_to_worklist used_regs
        | None ->
            (* This register is not defined within the function body,
               so it must be a function parameter. Parameters are implicitly
               live if they are used at all. No further action needed. *)
            ()
      end
    done;

    (* 3. Rebuild the function with only the live instructions. *)
    let new_blocks =
      List.map (fun bb ->
        let new_ops =
          List.filter (function
            | I_Instr instr ->
                (* Keep instruction if its result is live. Note that call
                   results were proactively marked live to preserve them. *)
                Hashtbl.mem live_regs instr.reg
            | I_Side_Effect (S_Store (addr, _)) ->
                (* A store is only kept if it's to a pointer that is
                   actually used, or not a known local alloca. *)
                (match addr with
                 | O_Reg p when is_alloca_reg p -> Hashtbl.mem used_pointers p
                 | _ -> true)
          ) bb.ops
        in
        { bb with ops = new_ops }
      ) f.blocks
    in

    { f with blocks = new_blocks; reg_types = f.reg_types }

end
