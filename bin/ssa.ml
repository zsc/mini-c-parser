(* file: ssa.ml *)

(*
  This file defines a custom Static Single Assignment (SSA) based
  Intermediate Representation (IR) and an associated Dead Code
  Elimination (DCE) optimization pass.

  This IR is designed to be independent of LLVM.
*)

open Ast

(*
  SSA IR Definition
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
    | O_CstI of int
    | O_CstF of float
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
    | D_ArrayAlloca of string * operand
    | D_GetElementPtr of operand * operand
    | D_SIToFP of operand (* Signed Integer to Floating Point conversion *)
    | D_FPToSI of operand (* Floating Point to Signed Integer conversion *)
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
    reg_types: (reg, Ast.c_type) Hashtbl.t;
  }

  (* A program is a list of function definitions. *)
  type program = func_def list

end


(*
  Dead Code Elimination (DCE) Pass
  ------------------------------------
  This pass removes instructions whose results are never used.
*)
module Dce = struct
  open Ssa

  (* Helper to extract all registers used by an operand. *)
  let used_regs_from_operand op =
    match op with
    | O_Reg r -> [r]
    | O_CstI _ | O_CstF _ | O_Global _ -> []

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
    | D_ArrayAlloca (_, size_op) -> used_regs_from_operand size_op
    | D_GetElementPtr (base, index) -> used_regs_from_operands [base; index]
    | D_SIToFP op -> used_regs_from_operand op
    | D_FPToSI op -> used_regs_from_operand op
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
      | Some { def = D_ArrayAlloca _; _ } -> true
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

(* AST to SSA Conversion *)
module Ast_to_ssa = struct
  open Ast
  open Ssa

  let get_pointee_type (ptr_type: Ast.c_type) : Ast.c_type =
    match ptr_type with
    | TPtr t -> t
    | _ -> failwith ("Ast_to_ssa: Cannot get pointee type of non-pointer type")

  let rec c_type_to_ll_string (t: c_type) : string =
    match t with
    | TVoid -> "void" | TChar -> "i8" | TInt -> "i32"
    | TFloat -> "float" | TDouble -> "double"
    | TPtr p -> (c_type_to_ll_string p) ^ "*"
    | TArray (_, _) -> failwith "c_type_to_ll_string should not be called on an array type"

  let func_return_types : (string, Ast.func_def) Hashtbl.t = Hashtbl.create 8
  type global_symbol_type =
    | GSymVar of Ast.c_type
    | GSymArray of Ast.c_type (* Element type *)

  let global_symbols : (string, global_symbol_type) Hashtbl.t = Hashtbl.create 8
  let global_strings : (string, string) Hashtbl.t = Hashtbl.create 8
  let string_counter = ref 0

  type ssa_builder_context = {
    (* Counters and context for the current function being built *)
    mutable reg_counter: int;
    mutable bbid_counter: int;
    var_map: (string, reg) Hashtbl.t; (* var name -> reg holding pointer *)
    mutable current_block_ops: operation list;
    mutable func_blocks: basic_block list;
    mutable current_bbid: bbid;
    mutable is_sealed: bool; (* true if the current block is terminated *)
    var_types: (string, Ast.c_type) Hashtbl.t; (* var name -> type *)
    reg_types: (reg, Ast.c_type) Hashtbl.t; (* reg -> type *)
  }

  let new_reg ctx = let i = ctx.reg_counter in ctx.reg_counter <- i + 1; R i
  let new_bbid ctx = let i = ctx.bbid_counter in ctx.bbid_counter <- i + 1; L i

  let create_ctx () = {
    reg_counter = 0;
    bbid_counter = 0;
    var_map = Hashtbl.create 16;
    current_block_ops = [];
    func_blocks = [];
    current_bbid = L (-1); (* Invalid initial bbid *)
    is_sealed = true; (* A new context has no open block to add to *)
    var_types = Hashtbl.create 16;
    reg_types = Hashtbl.create 64;
  }

  (* Finalizes the current basic block and adds it to the function's list *)
  let seal_block ctx term =
    let new_block = {
      id = ctx.current_bbid;
      ops = List.rev ctx.current_block_ops;
      term = term;
    } in
    ctx.func_blocks <- new_block :: ctx.func_blocks;
    ctx.current_block_ops <- [];
    ctx.is_sealed <- true;
    ()

  (* Starts a new basic block *)
  let start_new_block ctx =
    let bbid = new_bbid ctx in
    ctx.current_bbid <- bbid;
    ctx.is_sealed <- false;
    bbid

  let add_instr ctx def typ : reg =
    let reg = new_reg ctx in
    let instr = { reg; def } in
    ctx.current_block_ops <- I_Instr instr :: ctx.current_block_ops;
    Hashtbl.add ctx.reg_types reg typ;
    reg

  let get_string_label s =
    try Hashtbl.find global_strings s
    with Not_found ->
      let label = ".str." ^ string_of_int !string_counter in
      incr string_counter;
      Hashtbl.add global_strings s label;
      label

  let add_side_effect ctx sei =
    ctx.current_block_ops <- I_Side_Effect sei :: ctx.current_block_ops

  let rec convert_expr ctx (expr: Ast.expr) : operand * Ast.c_type =
    match expr with
    | CstI i -> (O_CstI i, TInt)
    | CstF f -> (O_CstF f, TDouble) (* C float literals are double by default *)
    | CstS s ->
        let label = get_string_label s in
        let ptr_type = TPtr TChar in
        (O_Global label, ptr_type)
    | Id s -> (* Can be a local var, a global var, or a global array name *)
      if Hashtbl.mem ctx.var_map s then (* Local variable or parameter *)
        let var_type = Hashtbl.find ctx.var_types s in
        let ptr_reg = Hashtbl.find ctx.var_map s in
        let res_reg = add_instr ctx (D_Load (O_Reg ptr_reg)) var_type in
        (O_Reg res_reg, var_type)
      else if Hashtbl.mem global_symbols s then (* Global symbol *)
        match Hashtbl.find global_symbols s with
        | GSymVar typ ->
            let res_reg = add_instr ctx (D_Load (O_Global s)) typ in
            (O_Reg res_reg, typ)
        | GSymArray elem_typ ->
            (O_Global s, TPtr elem_typ) (* Array name decays to pointer *)
      else
        failwith ("Undeclared identifier: " ^ s)
    | BinOp (op, e1, e2) ->
        let (op1, t1) = convert_expr ctx e1 in
        let (op2, t2) = convert_expr ctx e2 in
        let is_float_op = match t1, t2 with
          | TFloat, _ | TDouble, _ | _, TFloat | _, TDouble -> true
          | _, _ -> false
        in
        let final_type, final_op1, final_op2 =
          if is_float_op then
            let coerce_to_float op ty target_ty =
              if ty = TInt then O_Reg (add_instr ctx (D_SIToFP op) target_ty) else op
            in
            let float_type = if t1 = TDouble || t2 = TDouble then TDouble else TFloat in
            let new_op1 = coerce_to_float op1 t1 float_type in
            let new_op2 = coerce_to_float op2 t2 float_type in
            (float_type, new_op1, new_op2)
          else (t1, op1, op2) (* Assume int-like types *)
        in
        let res_reg = add_instr ctx (D_BinOp (op, final_op1, final_op2)) final_type in
        (O_Reg res_reg, final_type)
    | AddrOf e ->
        (match e with
         | Id s -> (* &var (local or global) *)
            if Hashtbl.mem ctx.var_map s then (* local *)
             let ptr_reg = Hashtbl.find ctx.var_map s in
             let var_type = Hashtbl.find ctx.var_types s in
             (O_Reg ptr_reg, TPtr var_type)
            else if Hashtbl.mem global_symbols s then (* global *)
              match Hashtbl.find global_symbols s with
              | GSymVar typ -> (O_Global s, TPtr typ)
              | GSymArray elem_typ -> (O_Global s, TPtr elem_typ) (* &arr is same as arr *)
            else failwith ("AST to SSA: Address of undeclared variable " ^ s)
         | Deref ptr_expr -> (* &( *p ) simplifies to p *)
             convert_expr ctx ptr_expr
         | ArrayAccess (base, index) -> (* &arr[i] *)
             let (base_op, base_type) = convert_expr ctx base in
             let (index_op, _) = convert_expr ctx index in
             let res_reg = add_instr ctx (D_GetElementPtr (base_op, index_op)) base_type in
             (O_Reg res_reg, base_type)
         | _ ->
             failwith "AST to SSA: Cannot take address of a non-lvalue expression")
    | Deref e -> (* *ptr_expr *)
        let (ptr_op, ptr_type) = convert_expr ctx e in
        let pointee_type = get_pointee_type ptr_type in
        let res_reg = add_instr ctx (D_Load ptr_op) pointee_type in
        (O_Reg res_reg, pointee_type)
    | Call (name, args) ->
        let arg_ops = List.map (fun e -> fst (convert_expr ctx e)) args in
        let func_info = try Hashtbl.find func_return_types name with Not_found -> failwith ("Call to undeclared function: " ^ name) in
        let res_reg = add_instr ctx (D_Call (name, arg_ops)) func_info.ret_type in
        (O_Reg res_reg, func_info.ret_type)
    | ArrayAccess (base, index) ->
        let (base_op, ptr_type) = convert_expr ctx base in
        let (index_op, _) = convert_expr ctx index in
        let elem_ptr_type = match ptr_type with
          | TPtr t -> TPtr t | _ -> failwith "Array access on non-pointer type"
        in
        let element_ptr_reg = add_instr ctx (D_GetElementPtr (base_op, index_op)) elem_ptr_type in
        let pointee_type = get_pointee_type elem_ptr_type in
        let res_reg = add_instr ctx (D_Load (O_Reg element_ptr_reg)) pointee_type in
        (O_Reg res_reg, pointee_type)

  let rec convert_stmt ctx (stmt: Ast.stmt) : unit =
    if ctx.is_sealed then () (* Unreachable code, do nothing *)
    else match stmt with
      | Return e ->
          let (op, _) = convert_expr ctx e in
          seal_block ctx (T_Ret op)
      | DoWhile (body, cond) ->
          (* The block currently being built is the loop's pre-header. *)
          (* Unconditionally jump to the body block. *)
          let body_bbid = new_bbid ctx in
          seal_block ctx (T_Br body_bbid);

          (* Loop body block *)
          ctx.current_bbid <- body_bbid; ctx.is_sealed <- false;
          convert_stmt ctx body;

          (* After the body, if it hasn't terminated, check the condition. *)
          if not ctx.is_sealed then (
              let (cond_op, _) = convert_expr ctx cond in
              let after_bbid = new_bbid ctx in
              seal_block ctx (T_CBr (cond_op, body_bbid, after_bbid));
              (* The new current block is the one after the loop. *)
              ctx.current_bbid <- after_bbid;
              ctx.is_sealed <- false
          ) (* else, the body terminated, so flow doesn't continue. The context remains sealed. *)
      | While (cond, body) ->
          (* The block currently being built is the loop's pre-header. *)
          (* We must end it and jump to the new condition-checking block. *)
          let cond_bbid = new_bbid ctx in
          seal_block ctx (T_Br cond_bbid);
          (* Condition block *)
          ctx.current_bbid <- cond_bbid;
          ctx.is_sealed <- false;
          let (cond_op, _) = convert_expr ctx cond in
          let body_bbid = new_bbid ctx in
          let after_bbid = new_bbid ctx in
          seal_block ctx (T_CBr (cond_op, body_bbid, after_bbid));

          (* Loop body block *)
          ctx.current_bbid <- body_bbid; ctx.is_sealed <- false;
          convert_stmt ctx body;
          if not ctx.is_sealed then seal_block ctx (T_Br cond_bbid); (* Jump back to condition *)

          (* After loop block *)
          ctx.current_bbid <- after_bbid; ctx.is_sealed <- false
      | If (cond, then_s, else_s_opt) ->
          let (cond_op, _) = convert_expr ctx cond in
          let then_bbid = new_bbid ctx in
          let else_bbid = new_bbid ctx in
          let merge_bbid = new_bbid ctx in
          let has_else = else_s_opt <> None in
          let else_dest = if has_else then else_bbid else merge_bbid in

          seal_block ctx (T_CBr (cond_op, then_bbid, else_dest));

          (* Then block *)
          ctx.current_bbid <- then_bbid;
          ctx.is_sealed <- false;
          convert_stmt ctx then_s;
          let then_reaches_merge = not ctx.is_sealed in
          if then_reaches_merge then
            seal_block ctx (T_Br merge_bbid);

          (* Else block *)
          let else_reaches_merge =
            match else_s_opt with
            | Some s ->
                ctx.current_bbid <- else_bbid;
                ctx.is_sealed <- false;
                convert_stmt ctx s;
                let reaches = not ctx.is_sealed in
                if reaches then seal_block ctx (T_Br merge_bbid);
                reaches
            | None -> true (* No 'else', so control flow always goes to merge block on false cond *)
          in

          (* The merge block becomes the new current block if it's reachable from either branch. *)
          if then_reaches_merge || else_reaches_merge then (
            ctx.current_bbid <- merge_bbid;
            ctx.is_sealed <- false
          ) (* Otherwise, both paths terminated, so subsequent code is unreachable and is_sealed is left as true. *)

    | Block stmts -> List.iter (convert_stmt ctx) stmts
    | Decl (_, name, init_opt) ->
        let ptr_reg = Hashtbl.find ctx.var_map name in (* Must have been pre-allocated *)
        (match init_opt with
         | Some e ->
             let (val_op, _) = convert_expr ctx e in
             add_side_effect ctx (S_Store (O_Reg ptr_reg, val_op))
         | None -> ())
    | Assign (lhs, rhs) ->
        let (rhs_op, rhs_type) = convert_expr ctx rhs in
        let get_lval_ptr_and_type = function
          | Id s ->
              if Hashtbl.mem ctx.var_map s then (* local *)
                (O_Reg (Hashtbl.find ctx.var_map s), Hashtbl.find ctx.var_types s)
              else if Hashtbl.mem global_symbols s then (* global *)
                match Hashtbl.find global_symbols s with
                | GSymVar typ -> (O_Global s, typ)
                | GSymArray _ -> failwith "AST to SSA: Cannot assign to an array name"
              else
                failwith ("Assignment to undeclared variable: " ^ s)
          | Deref ptr_expr -> let (addr_op, ptr_type) = convert_expr ctx ptr_expr in (addr_op, get_pointee_type ptr_type)
          | ArrayAccess (base, index) ->
              let (base_op, ptr_type) = convert_expr ctx base in
              let (index_op, _) = convert_expr ctx index in
              let elem_ptr_type = match ptr_type with TPtr t -> TPtr t | _ -> failwith "Array assign to non-pointer" in
              let elem_ptr_reg = add_instr ctx (D_GetElementPtr (base_op, index_op)) elem_ptr_type in
              (O_Reg elem_ptr_reg, get_pointee_type elem_ptr_type)
          | _ -> failwith "AST to SSA: Assignment to non-lvalue not implemented"
        in
        let (lval_ptr_op, lval_type) = get_lval_ptr_and_type lhs in
        let final_rhs_op = if lval_type <> rhs_type then (* Basic type coercion *)
          match lval_type, rhs_type with
          | (TFloat|TDouble), TInt -> O_Reg (add_instr ctx (D_SIToFP rhs_op) lval_type)
          | TInt, (TFloat|TDouble) -> O_Reg (add_instr ctx (D_FPToSI rhs_op) lval_type)
          | _, _ -> rhs_op
        else rhs_op
        in
        add_side_effect ctx (S_Store (lval_ptr_op, final_rhs_op))
    | ExprStmt e ->
        let _ = convert_expr ctx e in ()
    | ArrayDecl (_, _, _) -> () (* Handled in pre-allocation phase *)

  (* Finds all local variable and array declarations within a statement.
     Returns a list of (name, type, size_expr option).
     For `int x;`, size_expr is None.
     For `int arr[10];`, size_expr is Some(CstI 10). *)
  let rec find_all_decls_in_stmt (stmt: Ast.stmt) : (string * (Ast.c_type * Ast.expr option)) list =
    match stmt with
    | Decl (typ, name, _) -> [(name, (typ, None))]
    | ArrayDecl (typ, name, size) -> [(name, (typ, Some size))]
    | If (_, then_s, else_s_opt) ->
        let then_decls = find_all_decls_in_stmt then_s in
        let else_decls = match else_s_opt with Some s -> find_all_decls_in_stmt s | None -> [] in
        then_decls @ else_decls
    | DoWhile (body, _) -> find_all_decls_in_stmt body
    | While (_, body) -> find_all_decls_in_stmt body
    | Block stmts -> List.concat_map find_all_decls_in_stmt stmts
    | _ -> []

  let convert_func (fdef: Ast.func_def) : Ssa.func_def =
    let ctx = create_ctx () in

    (* Start the entry block *)
    let _ = start_new_block ctx in

    (* Gather all types of parameters and local variables *)
    let all_decls = find_all_decls_in_stmt fdef.body in
    List.iter (fun (typ, name) -> Hashtbl.add ctx.var_types name typ) fdef.params;
    List.iter (fun (name, (typ, _)) -> Hashtbl.add ctx.var_types name typ) all_decls;

    (* Process parameters *)
    let param_regs = List.map (fun (param_type, name) ->
        let param_val_reg = new_reg ctx in (* This will hold the incoming value *)
        Hashtbl.add ctx.reg_types param_val_reg param_type;
        let ptr_reg = add_instr ctx (D_Alloca (c_type_to_ll_string param_type)) (TPtr param_type) in
        add_side_effect ctx (S_Store (O_Reg ptr_reg, O_Reg param_val_reg));
        Hashtbl.add ctx.var_map name ptr_reg;
        param_val_reg
      ) fdef.params
    in

    (* Allocate space for all local variables *)
    List.iter (fun (name, (typ, size_opt)) ->
      if not (Hashtbl.mem ctx.var_map name) then
        let ptr_reg = match size_opt with
          | None -> add_instr ctx (D_Alloca (c_type_to_ll_string typ)) (TPtr typ)
          | Some size_expr ->
              let (size_op, _) = convert_expr ctx size_expr in (* Array address has type TPtr(elem_type) *)
              add_instr ctx (D_ArrayAlloca (c_type_to_ll_string typ, size_op)) (TPtr typ)
        in
        Hashtbl.add ctx.var_map name ptr_reg) all_decls;

    (* Convert the function body *)
    convert_stmt ctx fdef.body;

    (* If the last block wasn't terminated, it implies the C function could
       flow off the end without a return, which is undefined behavior.
       We add a default return to make the IR well-formed. *)
    if not ctx.is_sealed then begin
       if fdef.ret_type = TVoid then
         seal_block ctx (T_Ret (O_CstI 0)) (* Dummy for void, LLVM codegen will handle it *)
       else
         seal_block ctx (T_Ret (O_CstI 0)) (* Default return 0 for non-void *)
    end;

    {
      name = fdef.name;
      params = param_regs;
      blocks = List.rev ctx.func_blocks;
      reg_types = ctx.reg_types;
    }

  let convert_program (prog: Ast.program) : (global_def list * Ssa.program) =
    (* First pass: collect all function signatures and global symbols *)
    Hashtbl.clear func_return_types;
    Hashtbl.clear global_symbols;
    Hashtbl.clear global_strings;
    string_counter := 0;
    List.iter (function
      | GFunc fdef -> Hashtbl.add func_return_types fdef.name fdef
      | GVar (typ, name, _) -> Hashtbl.add global_symbols name (GSymVar typ)
      | GArray (typ, name, _) -> Hashtbl.add global_symbols name (GSymArray typ)
    ) prog;

    (* Second pass: convert all functions to SSA *)
    let ssa_functions = List.filter_map (function
      | GFunc fdef -> Some (convert_func fdef)
      | _ -> None
    ) prog in
    let global_defs = List.filter (function GFunc _ -> false | _ -> true) prog in
    (global_defs, ssa_functions)
end

(* SSA IR Pretty Printer (for debugging) *)
module Ssa_printer = struct
  open Ssa

  let rec string_of_c_type (t: Ast.c_type) : string =
    match t with
    | TVoid -> "void" | TChar -> "char" | TInt -> "int"
    | TFloat -> "float" | TDouble -> "double"
    | TPtr p -> (string_of_c_type p) ^ "*"
    | TArray (elem_t, size) -> Printf.sprintf "%s[%d]" (string_of_c_type elem_t) size

  let string_of_reg (R i) = "%r" ^ string_of_int i
  let string_of_bbid (L i) = "L" ^ string_of_int i
  let string_of_operand = function
    | O_CstI i -> string_of_int i
    | O_CstF f -> string_of_float f
    | O_Reg r -> string_of_reg r
    | O_Global s -> "@" ^ s

  let string_of_binop = function
    | Add -> "add" | Sub -> "sub" | Mul -> "mul" | Div -> "div"
    | Mod -> "mod" | BitAnd -> "and" | BitOr -> "or" | BitXor -> "xor"
    | Le -> "le" | Eq -> "eq" | Ne -> "ne" | Lt -> "lt" | Gt -> "gt" | Ge -> "ge"

  let string_of_definition def =
    match def with
    | D_BinOp (op, o1, o2) -> Printf.sprintf "%s %s, %s" (string_of_binop op) (string_of_operand o1) (string_of_operand o2)
    | D_Call (name, args) -> Printf.sprintf "call @%s(%s)" name (String.concat ", " (List.map string_of_operand args))
    | D_Phi phis -> "phi " ^ (String.concat ", " (List.map (fun (op, bbid) -> Printf.sprintf "[ %s, %s ]" (string_of_operand op) (string_of_bbid bbid)) phis))
    | D_Alloca typ -> Printf.sprintf "alloca %s" typ
    | D_ArrayAlloca (typ, size) -> Printf.sprintf "alloca %s, %s" typ (string_of_operand size)
    | D_SIToFP op -> Printf.sprintf "sitofp %s" (string_of_operand op)
    | D_FPToSI op -> Printf.sprintf "fptosi %s" (string_of_operand op)
    | D_GetElementPtr (base, index) -> Printf.sprintf "getelementptr %s, %s" (string_of_operand base) (string_of_operand index)
    | D_Load op -> Printf.sprintf "load %s" (string_of_operand op)

  let string_of_instruction instr =
    Printf.sprintf "  %s = %s" (string_of_reg instr.reg) (string_of_definition instr.def)

  let string_of_side_effect sei =
    match sei with
    | S_Store (addr, value) ->
      Printf.sprintf "  store %s, %s" (string_of_operand value) (string_of_operand addr)

  let string_of_terminator term =
    "  " ^ match term with
    | T_Ret op -> "ret " ^ string_of_operand op
    | T_Br bbid -> "br " ^ string_of_bbid bbid
    | T_CBr (cond, ltrue, lfalse) -> Printf.sprintf "cbr %s, %s, %s" (string_of_operand cond) (string_of_bbid ltrue) (string_of_bbid lfalse)

  let string_of_basic_block bb =
    let ops_str = String.concat "\n" (List.map (function
      | I_Instr i -> string_of_instruction i
      | I_Side_Effect s -> string_of_side_effect s
      ) bb.ops) in
    let parts = [string_of_bbid bb.id ^ ":"; ops_str; string_of_terminator bb.term] in
    String.concat "\n" (List.filter (fun s -> s <> "") parts)

  let string_of_func_def f =
    let params_str = String.concat ", " (List.map string_of_reg f.params) in
    let blocks_str = String.concat "\n\n" (List.map string_of_basic_block f.blocks) in
    let type_annots = Hashtbl.fold (fun r t acc ->
        Printf.sprintf "; %s : %s" (string_of_reg r) (string_of_c_type t) :: acc
      ) f.reg_types [] in
    Printf.sprintf "define @%s(%s) {\n%s\n\n%s\n}" f.name params_str (String.concat "\n" (List.rev type_annots)) blocks_str

  let string_of_program prog =
    String.concat "\n\n" (List.map string_of_func_def prog)
end
