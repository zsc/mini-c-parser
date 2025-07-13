(* file: main.ml *)

(*
  OCaml Mini-C Compiler to LLVM IR
  =================================

  To compile and run:
  1. Make sure you have the 'str' library (usually included with OCaml).
     If not: `opam install str`
  2. Compile: `ocamlfind ocamlopt -package str -linkpkg -o compiler main.ml`
     (or `ocamlbuild -use-ocamlfind -pkg str compiler.native`)
  3. Run: `./compiler`

  The program will parse the hardcoded C source, print the AST,
  and then print the generated LLVM IR as a string.
*)

open Ast
open Ssa


(* II. Tokenizer (Lexer) *)
(* (Unaltered) *)

type token =
  | T_Int | T_Return | T_If | T_Else | T_While | T_For
  | T_Id of string | T_Num of int
  | T_Plus | T_Minus | T_Star | T_Slash | T_Le | T_Eq | T_Ne | T_Lt | T_Gt | T_Ge
  | T_Lparen | T_Rparen | T_Assign | T_Lbrace | T_Rbrace | T_Lbracket | T_Rbracket | T_Ampersand
  | T_Comma | T_Semicolon | T_Eof

let keyword_map = [
  ("int", T_Int); ("return", T_Return); ("if", T_If); ("else", T_Else);
  ("while", T_While); ("for", T_For)
]

let token_specs = [
  (Str.regexp "[ \t\n\r]+", fun _ -> None); (Str.regexp "//[^\n]*", fun _ -> None); (Str.regexp "/\\*.*?\\*/", fun _ -> None);
  (Str.regexp "[a-zA-Z_][a-zA-Z0-9_]*", fun s -> try Some (List.assoc s keyword_map) with Not_found -> Some (T_Id s));
  (Str.regexp "[0-9]+", fun s -> Some (T_Num (int_of_string s)));
  (Str.regexp "<=", fun _ -> Some T_Le); (Str.regexp "==", fun _ -> Some T_Eq); (Str.regexp "!=", fun _ -> Some T_Ne);
  (Str.regexp ">=", fun _ -> Some T_Ge); (Str.regexp "<", fun _ -> Some T_Lt); (Str.regexp ">", fun _ -> Some T_Gt);
  (Str.regexp "+", fun _ -> Some T_Plus); (Str.regexp "-", fun _ -> Some T_Minus); (Str.regexp "&", fun _ -> Some T_Ampersand); (Str.regexp "=", fun _ -> Some T_Assign);
  (Str.regexp "*", fun _ -> Some T_Star); (Str.regexp "/", fun _ -> Some T_Slash); (Str.regexp "(", fun _ -> Some T_Lparen);
  (Str.regexp ")", fun _ -> Some T_Rparen); (Str.regexp "{", fun _ -> Some T_Lbrace); (Str.regexp "}", fun _ -> Some T_Rbrace);
  (Str.regexp "\\[", fun _ -> Some T_Lbracket); (Str.regexp "\\]", fun _ -> Some T_Rbracket);
  (Str.regexp ",", fun _ -> Some T_Comma); (Str.regexp ";", fun _ -> Some T_Semicolon);
]

let tokenize str =
  let rec next_token pos =
    if pos >= String.length str then [T_Eof]
    else
      let rec find_match = function
        | [] -> failwith ("Lexer error: Unrecognized character at position " ^ string_of_int pos)
        | (re, action) :: rest_specs ->
            if Str.string_match re str pos then
              let matched = Str.matched_string str in
              let new_pos = Str.match_end () in
              match action matched with
              | Some token -> token :: next_token new_pos
              | None -> next_token new_pos
            else find_match rest_specs
      in find_match token_specs
  in next_token 0

(* III. Parser *)
(* (Unaltered) *)

exception Parser_error of string

let fail_parse msg = raise (Parser_error msg)

let string_of_token = function
  | T_Int -> "T_Int" | T_Return -> "T_Return" | T_If -> "T_If" | T_Else -> "T_Else" | T_While -> "T_While" | T_For -> "T_For"
  | T_Id s -> Printf.sprintf "T_Id(%s)" s | T_Num n -> Printf.sprintf "T_Num(%d)" n
  | T_Plus -> "T_Plus" | T_Minus -> "T_Minus" | T_Star -> "T_Star" | T_Slash -> "T_Slash"
  | T_Le -> "T_Le" | T_Eq -> "T_Eq" | T_Ne -> "T_Ne" | T_Lt -> "T_Lt" | T_Gt -> "T_Gt" | T_Ge -> "T_Ge"
  | T_Lparen -> "T_Lparen" | T_Rparen -> "T_Rparen" | T_Assign -> "T_Assign"
  | T_Lbrace -> "T_Lbrace" | T_Rbrace -> "T_Rbrace" | T_Lbracket -> "T_Lbracket" | T_Rbracket -> "T_Rbracket"
  | T_Ampersand -> "T_Ampersand"
  | T_Comma -> "T_Comma" | T_Semicolon -> "T_Semicolon" | T_Eof -> "T_Eof"

let expect token tokens =
  match tokens with
  | t :: rest when t = token -> rest
  | t :: _ -> fail_parse (Printf.sprintf "Expected token %s but found %s" (string_of_token token) (string_of_token t))
  | [] -> fail_parse "Unexpected end of input"

let rec parse_program tokens : program * token list =
  match tokens with
  | T_Eof :: _ -> ([], tokens)
  | _ ->
      let (def, rest_tokens) = parse_top_level_def tokens in
      let (defs, final_tokens) = parse_program rest_tokens in
      (def :: defs, final_tokens)

and parse_top_level_def tokens =
  let rest1 = match tokens with T_Int :: r -> r | _ -> fail_parse "Expected 'int' as return type" in
  let name, rest2 = match rest1 with T_Id s :: rest -> s, rest | _ -> fail_parse "Expected function name" in
  let rest3 = expect T_Lparen rest2 in
  let params, rest4 = parse_params rest3 in
  let rest5 = expect T_Rparen rest4 in
  let body, rest6 = parse_stmt rest5 in
  ({ ret_type = "int"; name; params; body }, rest6)

and parse_type_name tokens = match tokens with
  | T_Int :: rest ->
      let rec parse_pointers base_type toks =
        match toks with
        | T_Star :: r -> parse_pointers (base_type ^ "*") r
        | _ -> (base_type, toks)
      in
      parse_pointers "int" rest
  | _ -> fail_parse "Expected 'int' as base type"

and parse_params tokens = match tokens with
  | T_Rparen :: _ -> ([], tokens)
  | _ ->
      let rec loop acc tokens =
        let (param_type, rest1) = parse_type_name tokens in
        let name, rest2 = match rest1 with T_Id s :: rest -> s, rest | _ -> fail_parse "Expected parameter name" in
        let new_acc = acc @ [(param_type, name)] in
        match rest2 with T_Comma :: rest' -> loop new_acc rest' | _ -> (new_acc, rest2)
      in loop [] tokens

and parse_stmt tokens = match tokens with
  | T_Return :: rest ->
      let (expr, rest') = parse_expr rest in
      let rest'' = expect T_Semicolon rest' in
      (Return expr, rest'')
  | T_If :: rest ->
      let rest1 = expect T_Lparen rest in
      let (cond, rest2) = parse_expr rest1 in
      let rest3 = expect T_Rparen rest2 in
      let (then_stmt, rest4) = parse_stmt rest3 in
      let (else_stmt, rest_final) = match rest4 with
        | T_Else :: rest' -> let (stmt, rest'') = parse_stmt rest' in (Some stmt, rest'')
        | _ -> (None, rest4) in
      (If (cond, then_stmt, else_stmt), rest_final)
  | T_While :: rest ->
      let rest1 = expect T_Lparen rest in
      let (cond, rest2) = parse_expr rest1 in
      let rest3 = expect T_Rparen rest2 in
      let (body, rest_final) = parse_stmt rest3 in
      (While (cond, body), rest_final)
  | T_For :: rest -> (* Desugar for loop into a while loop *)
      let rest1 = expect T_Lparen rest in
      (* Parse initializer: can be a declaration or expression stmt *)
      let (init_stmt, rest2) = if List.hd rest1 = T_Semicolon then (Block [], rest1)
                               else (let (s, r) = parse_stmt rest1 in (s,r)) in
      let rest3 = expect T_Semicolon rest2 in
      (* Parse condition *)
      let (cond_expr, rest4) = if List.hd rest3 = T_Semicolon then (Cst 1, rest3) (* Empty cond is true *)
                               else parse_expr rest3 in
      let rest5 = expect T_Semicolon rest4 in
      (* Parse post-loop expression *)
      let (post_expr_opt, rest6) = if List.hd rest5 = T_Rparen then (None, rest5)
                                   else (let (e,r) = parse_expr rest5 in (Some e, r)) in
      let rest7 = expect T_Rparen rest6 in
      let (body_stmt, rest_final) = parse_stmt rest7 in
      (* Desugar: { init; while(cond) { body; post; } } *)
      let post_stmt_opt = match post_expr_opt with
        | Some e -> Some (ExprStmt e)
        | None -> None in
      let new_body = Block (match post_stmt_opt with Some s -> [body_stmt; s] | None -> [body_stmt]) in
      let while_loop = While (cond_expr, new_body) in
      (Block [init_stmt; while_loop], rest_final)
  | T_Lbrace :: rest ->
      let rec parse_stmts acc t = match t with
        | T_Rbrace :: rest' -> (Block (List.rev acc), rest')
        | _ -> let (stmt, t') = parse_stmt t in parse_stmts (stmt :: acc) t'
      in parse_stmts [] rest
  | T_Int :: _ ->
      let (decl_type, rest_type) = parse_type_name tokens in
      let name, rest_name = match rest_type with T_Id s :: r -> s, r | _ -> fail_parse "Expected identifier in declaration" in
      (match rest_name with
       | T_Lbracket :: r ->
           let (size_expr, r') = parse_expr r in
           let r'' = expect T_Rbracket r' in
           let r_final = expect T_Semicolon r'' in
           (ArrayDecl (decl_type, name, size_expr), r_final)
       | T_Assign :: r ->
           let (init_expr, r') = parse_expr r in
           let r_final = expect T_Semicolon r' in
           (Decl (decl_type, name, Some init_expr), r_final)
       | T_Semicolon :: r_final -> (Decl (decl_type, name, None), r_final) (* Corrected this line to align properly in git diff, no functional change *)
       | _ -> fail_parse "Malformed declaration")
  | T_Id _ :: _ -> (* Match if the first token is an Id, then parse the expression from the original tokens list *)
      let (lhs_expr, rest_expr) = parse_expr tokens in
      (match rest_expr with
        | T_Assign :: rest_assign ->
            let (rhs_expr, rest_rhs) = parse_expr rest_assign in
            let rest_final = expect T_Semicolon rest_rhs in
            (Assign(lhs_expr, rhs_expr), rest_final)
        | T_Semicolon :: rest_final -> (ExprStmt lhs_expr, rest_final)
        | _ -> fail_parse "Expected '=' or ';' after expression statement")
  | _ -> fail_parse "Unexpected token at start of statement"

and parse_expr tokens = parse_assign_expr tokens
and parse_assign_expr tokens = parse_equality_expr tokens
and parse_equality_expr tokens =
  let rec loop lhs toks = match toks with
    | T_Eq :: r -> let (rhs, r') = parse_relational_expr r in loop (BinOp (Eq, lhs, rhs)) r'
    | T_Ne :: r -> let (rhs, r') = parse_relational_expr r in loop (BinOp (Ne, lhs, rhs)) r'
    | _ -> (lhs, toks)
  in let (lhs, r) = parse_relational_expr tokens in loop lhs r
and parse_relational_expr tokens =
  let rec loop lhs toks = match toks with
    | T_Lt :: r -> let (rhs, r') = parse_additive_expr r in loop (BinOp (Lt, lhs, rhs)) r'
    | T_Le :: r -> let (rhs, r') = parse_additive_expr r in loop (BinOp (Le, lhs, rhs)) r'
    | T_Gt :: r -> let (rhs, r') = parse_additive_expr r in loop (BinOp (Gt, lhs, rhs)) r'
    | T_Ge :: r -> let (rhs, r') = parse_additive_expr r in loop (BinOp (Ge, lhs, rhs)) r'
    | _ -> (lhs, toks)
  in let (lhs, r) = parse_additive_expr tokens in loop lhs r
and parse_additive_expr tokens =
  let rec loop lhs toks = match toks with
    | T_Plus :: r -> let (rhs, r') = parse_multiplicative_expr r in loop (BinOp (Add, lhs, rhs)) r'
    | T_Minus :: r -> let (rhs, r') = parse_multiplicative_expr r in loop (BinOp (Sub, lhs, rhs)) r'
    | _ -> (lhs, toks)
  in let (lhs, r) = parse_multiplicative_expr tokens in loop lhs r
and parse_multiplicative_expr tokens =
  let rec loop lhs toks = match toks with
    | T_Star :: r -> let (rhs, r') = parse_unary_expr r in loop (BinOp (Mul, lhs, rhs)) r'
    | T_Slash :: r -> let (rhs, r') = parse_unary_expr r in loop (BinOp (Div, lhs, rhs)) r'
    | _ -> (lhs, toks)
  in let (lhs, r) = parse_unary_expr tokens in loop lhs r
and parse_unary_expr tokens = match tokens with
  | T_Minus :: r -> let (e, r') = parse_unary_expr r in (BinOp (Sub, Cst 0, e), r')
  | T_Plus :: r -> parse_unary_expr r
  | T_Ampersand :: r -> let (e, r') = parse_unary_expr r in (AddrOf e, r')
  | T_Star :: r -> let (e, r') = parse_unary_expr r in (Deref e, r')
  | _ -> parse_postfix_expr tokens
and parse_postfix_expr tokens =
  let (base, rest) = parse_primary_expr tokens in
  let rec loop base_expr tokens =
    match tokens with
    | T_Lparen :: _ -> (* Function call *)
        let func_name = match base_expr with Id s -> s | _ -> fail_parse "Function name must be an identifier" in
        let rest1 = expect T_Lparen tokens in
        let (args, rest2) = parse_args rest1 in
        let rest3 = expect T_Rparen rest2 in
        loop (Call (func_name, args)) rest3
    | T_Lbracket :: rest -> (* Array access *)
        let (index_expr, rest') = parse_expr rest in
        let rest'' = expect T_Rbracket rest' in
        loop (ArrayAccess (base_expr, index_expr)) rest''
    | _ -> (base_expr, tokens)
  in loop base rest
and parse_primary_expr tokens = match tokens with
  | T_Num n :: rest -> (Cst n, rest)
  | T_Id s :: rest -> (Id s, rest)
  | T_Lparen :: rest ->
      let (e, rest') = parse_expr rest in
      let rest'' = expect T_Rparen rest' in
      (e, rest'')
  | _ -> fail_parse "Unexpected token in primary expression"
and parse_args tokens = match tokens with
  | T_Rparen :: _ -> ([], tokens)
  | _ -> let rec loop acc toks =
           let (arg, toks') = parse_expr toks in
           let new_acc = acc @ [arg] in
           match toks' with T_Comma :: rest -> loop new_acc rest | _ -> (new_acc, toks')
         in loop [] tokens

let parse_from_string str =
  try
    let tokens = tokenize str in
    match parse_program tokens with
    | ast, (T_Eof :: _) -> Ok ast
    | _, t :: _ -> Error (Printf.sprintf "Parser error: Did not consume all tokens, starting with %s." (string_of_token t))
    | _ -> Error "Parser error: Unknown (unexpected tokens remaining)."
  with
  | Parser_error msg -> Error ("Parser error: " ^ msg)
  | Failure msg -> Error ("Lexer/Parser failure: " ^ msg)

(* IV. AST to SSA Conversion *)
module Ast_to_ssa = struct
  open Ast
  open Ssa

  type ssa_builder_context = {
    mutable reg_counter: int;
    mutable bbid_counter: int;
    var_map: (string, reg) Hashtbl.t; (* var name -> reg holding pointer *)
    mutable current_block_ops: operation list;
    mutable func_blocks: basic_block list;
    mutable current_bbid: bbid;
    mutable is_sealed: bool; (* true if the current block is terminated *)
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

  let add_instr ctx def =
    let reg = new_reg ctx in
    let instr = { reg; def } in
    ctx.current_block_ops <- I_Instr instr :: ctx.current_block_ops;
    reg

  let add_side_effect ctx sei =
    ctx.current_block_ops <- I_Side_Effect sei :: ctx.current_block_ops

  let rec convert_expr ctx (expr: Ast.expr) : operand =
    match expr with
    | Cst i -> O_Cst i
    | Id s ->
        let ptr_reg = Hashtbl.find ctx.var_map s in
        let res_reg = add_instr ctx (D_Load (O_Reg ptr_reg)) in
        O_Reg res_reg
    | BinOp (op, e1, e2) ->
        let op1 = convert_expr ctx e1 in
        let op2 = convert_expr ctx e2 in
        let res_reg = add_instr ctx (D_BinOp (op, op1, op2)) in
        O_Reg res_reg
    | AddrOf e ->
        (match e with
         | Id s -> (* &var *)
             let ptr_reg = Hashtbl.find ctx.var_map s in
             O_Reg ptr_reg
         | Deref ptr_expr -> (* &( *p ) simplifies to p *)
             convert_expr ctx ptr_expr
         | ArrayAccess (_, _) ->
             failwith "AST to SSA: Address of array element not implemented"
         | _ ->
             failwith "AST to SSA: Cannot take address of a non-lvalue expression")
    | Deref e -> (* *ptr_expr *)
        let ptr_op = convert_expr ctx e in
        let res_reg = add_instr ctx (D_Load ptr_op) in
        O_Reg res_reg
    | Call (name, args) ->
        let arg_ops = List.map (convert_expr ctx) args in
        let res_reg = add_instr ctx (D_Call (name, arg_ops)) in
        O_Reg res_reg
    | ArrayAccess (_, _) -> failwith "AST to SSA: Array access not implemented"

  let rec convert_stmt ctx (stmt: Ast.stmt) : unit =
    if ctx.is_sealed then () (* Unreachable code, do nothing *)
    else match stmt with
      | Return e ->
          let op = convert_expr ctx e in
          seal_block ctx (T_Ret op)
      | While (cond, body) ->
          let cond_bbid = start_new_block ctx in
          seal_block ctx (T_Br cond_bbid); (* Jump to condition check *)

          (* Condition block *)
          ctx.current_bbid <- cond_bbid;
          ctx.is_sealed <- false;
          let cond_op = convert_expr ctx cond in
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
          let cond_op = convert_expr ctx cond in
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
             let val_op = convert_expr ctx e in
             add_side_effect ctx (S_Store (O_Reg ptr_reg, val_op))
         | None -> ())
    | Assign (lhs, rhs) ->
        let rhs_op = convert_expr ctx rhs in
        (match lhs with
         | Id s ->
             let ptr_reg = Hashtbl.find ctx.var_map s in
             add_side_effect ctx (S_Store (O_Reg ptr_reg, rhs_op))
         | Deref ptr_expr ->
             let addr_op = convert_expr ctx ptr_expr in
             add_side_effect ctx (S_Store (addr_op, rhs_op))
         | _ -> failwith "AST to SSA: Assignment to non-variable not implemented")
    | ExprStmt e ->
        let _ = convert_expr ctx e in ()
    | ArrayDecl _ -> failwith "AST to SSA: Array declaration not implemented"

  let rec find_decls_in_stmt (stmt: Ast.stmt) : string list =
    match stmt with
    | Decl (_, name, _) -> [name]
    | ArrayDecl (_, name, _) -> [name]
    | If (_, then_s, else_s_opt) ->
        let then_decls = find_decls_in_stmt then_s in
        let else_decls = match else_s_opt with Some s -> find_decls_in_stmt s | None -> [] in
        then_decls @ else_decls
    | Block stmts -> List.concat_map find_decls_in_stmt stmts
    | _ -> []

  let convert_func (fdef: Ast.top_level_def) : Ssa.func_def =
    let ctx = create_ctx () in

    (* Start the entry block *)
    let _ = start_new_block ctx in

    (* Process parameters *)
    let param_regs = List.map (fun (_, name) ->
        let param_val_reg = new_reg ctx in (* This will hold the incoming value *)
        let ptr_reg = add_instr ctx D_Alloca in
        add_side_effect ctx (S_Store (O_Reg ptr_reg, O_Reg param_val_reg));
        Hashtbl.add ctx.var_map name ptr_reg;
        param_val_reg
      ) fdef.params
    in

    (* Allocate space for all local variables *)
    let local_vars = find_decls_in_stmt fdef.body in
    List.iter (fun name ->
        let ptr_reg = add_instr ctx D_Alloca in
        Hashtbl.add ctx.var_map name ptr_reg;
      ) local_vars;

    (* Convert the function body *)
    convert_stmt ctx fdef.body;

    (* If the last block wasn't terminated, it implies the C function could
       flow off the end without a return, which is undefined behavior.
       We add a default return to make the IR well-formed. *)
    if not ctx.is_sealed then begin
       seal_block ctx (T_Ret (O_Cst 0))
    end;

    {
      name = fdef.name;
      params = param_regs;
      blocks = List.rev ctx.func_blocks;
    }

  let convert_program (prog: Ast.program) : Ssa.program =
    List.map convert_func prog
end

(* V. SSA IR Pretty Printer (for debugging) *)
module Ssa_printer = struct
  open Ssa

  let string_of_reg (R i) = "%r" ^ string_of_int i
  let string_of_bbid (L i) = "L" ^ string_of_int i
  let string_of_operand = function
    | O_Cst i -> string_of_int i
    | O_Reg r -> string_of_reg r
    | O_Global s -> "@" ^ s

  let string_of_binop = function
    | Add -> "add" | Sub -> "sub" | Mul -> "mul" | Div -> "div"
    | Le -> "le" | Eq -> "eq" | Ne -> "ne" | Lt -> "lt" | Gt -> "gt" | Ge -> "ge"

  let string_of_definition def =
    match def with
    | D_BinOp (op, o1, o2) -> Printf.sprintf "%s %s, %s" (string_of_binop op) (string_of_operand o1) (string_of_operand o2)
    | D_Call (name, args) -> Printf.sprintf "call @%s(%s)" name (String.concat ", " (List.map string_of_operand args))
    | D_Phi phis -> "phi " ^ (String.concat ", " (List.map (fun (op, bbid) -> Printf.sprintf "[ %s, %s ]" (string_of_operand op) (string_of_bbid bbid)) phis))
    | D_Alloca -> "alloca"
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
    Printf.sprintf "define @%s(%s) {\n%s\n}" f.name params_str blocks_str

  let string_of_program prog =
    String.concat "\n\n" (List.map string_of_func_def prog)
end

(* VI. Code Generation (from SSA to LLVM IR) *)
module Codegen = struct
  open Ssa

  let string_of_ssa_reg (R i) = "%r" ^ string_of_int i
  let string_of_ssa_bbid (L i) = "L" ^ string_of_int i

  let string_of_ssa_operand (op: operand) : string =
    match op with
    | O_Cst i -> string_of_int i
    | O_Reg r -> string_of_ssa_reg r
    | O_Global s -> "@" ^ s

  let ll_binop = function
    | Add -> "add nsw"
    | Sub -> "sub nsw"
    | Mul -> "mul nsw"
    | Div -> "sdiv"
    | Lt  -> "icmp slt"
    | Le  -> "icmp sle"
    | Gt  -> "icmp sgt"
    | Ge  -> "icmp sge"
    | Eq  -> "icmp eq"
    | Ne  -> "icmp ne"

  let codegen_instr (instr: instruction) : string list =
    let dest_reg = string_of_ssa_reg instr.reg in
    match instr.def with
    | D_BinOp (op, o1, o2) ->
        let op_str = ll_binop op in
        let s_op1 = string_of_ssa_operand o1 in
        let s_op2 = string_of_ssa_operand o2 in
        let is_comparison = match op with Lt|Le|Gt|Ge|Eq|Ne -> true | _ -> false in
        if is_comparison then
          let i1_res = dest_reg ^ ".i1" in
          let cmp_instr = Printf.sprintf "  %s = %s i32 %s, %s" i1_res op_str s_op1 s_op2 in
          let zext_instr = Printf.sprintf "  %s = zext i1 %s to i32" dest_reg i1_res in
          [cmp_instr; zext_instr]
        else
          [Printf.sprintf "  %s = %s i32 %s, %s" dest_reg op_str s_op1 s_op2]
    | D_Call (name, args) ->
        let arg_strs = List.map (fun op -> "i32 " ^ string_of_ssa_operand op) args in
        [Printf.sprintf "  %s = call i32 @%s(%s)" dest_reg name (String.concat ", " arg_strs)]
    | D_Phi _ -> failwith "LLVM Codegen: Phi nodes not supported in this simplified compiler"
    | D_Alloca ->
        [Printf.sprintf "  %s = alloca i32, align 4" dest_reg]
    | D_Load addr_op ->
        let s_addr = string_of_ssa_operand addr_op in
        [Printf.sprintf "  %s = load i32, i32* %s, align 4" dest_reg s_addr]

  let codegen_side_effect (sei: side_effect_instr) : string =
    match sei with
    | S_Store (addr_op, val_op) ->
        let s_addr = string_of_ssa_operand addr_op in
        let s_val = string_of_ssa_operand val_op in
        Printf.sprintf "  store i32 %s, i32* %s, align 4" s_val s_addr

  let codegen_terminator (term: terminator) : string list =
    match term with
    | T_Ret op -> [Printf.sprintf "  ret i32 %s" (string_of_ssa_operand op)]
    | T_Br bbid -> [Printf.sprintf "  br label %%%s" (string_of_ssa_bbid bbid)]
    | T_CBr (cond_op, ltrue, lfalse) ->
        let s_cond = string_of_ssa_operand cond_op in
        let i1_res_for_br = s_cond ^ ".br_cond" in
        let cmp_instr = Printf.sprintf "  %s = icmp ne i32 %s, 0" i1_res_for_br s_cond in
        let br_instr = Printf.sprintf "  br i1 %s, label %%%s, label %%%s" i1_res_for_br (string_of_ssa_bbid ltrue) (string_of_ssa_bbid lfalse) in
        [cmp_instr; br_instr]

  let codegen_bb (bb: basic_block) : string list =
    let label = (string_of_ssa_bbid bb.id) ^ ":" in
    let ops_code = List.concat_map (function
      | I_Instr i -> codegen_instr i
      | I_Side_Effect s -> [codegen_side_effect s]
      ) bb.ops in
    let term = codegen_terminator bb.term in
    [label] @ ops_code @ term

  let codegen_func (f: func_def) : string =
    let param_strs = List.map (fun r -> "i32 " ^ string_of_ssa_reg r) f.params in
    let signature = Printf.sprintf "define i32 @%s(%s) {" f.name (String.concat ", " param_strs) in
    let body_lines = List.concat_map codegen_bb f.blocks in
    String.concat "\n" ([signature] @ body_lines @ ["}"])

  let codegen_program (prog: Ssa.program) : (string, string) result =
    try
        let func_defs = List.map codegen_func prog in
        let full_module = String.concat "\n\n" func_defs in
        Ok full_module
    with
    | Failure msg -> Error ("Codegen failed: " ^ msg)
end

(* VII. AST Pretty Printer (for debugging) *)
let rec string_of_expr = function
  | Cst n -> string_of_int n | Id s -> s
  | BinOp (op, e1, e2) ->
      let op_str = match op with Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"
        | Le -> "<=" | Eq -> "==" | Ne -> "!=" | Lt -> "<" | Gt -> ">" | Ge -> ">=" in
      Printf.sprintf "(%s %s %s)" (string_of_expr e1) op_str (string_of_expr e2)
  | Call (n, args) -> Printf.sprintf "%s(%s)" n (String.concat ", " (List.map string_of_expr args))
  | AddrOf e -> "&(" ^ (string_of_expr e) ^ ")"
  | Deref e -> "*(" ^ (string_of_expr e) ^ ")"
  | ArrayAccess (b, i) -> Printf.sprintf "%s[%s]" (string_of_expr b) (string_of_expr i)

let rec string_of_stmt indent = function
  | Return e -> indent ^ "Return " ^ (string_of_expr e) ^ ";"
  | While (c, b) -> indent ^ "While (" ^ (string_of_expr c) ^ ")\n" ^ (string_of_stmt (indent ^ "  ") b)
  | If (c, t, e_opt) ->
      let else_str = match e_opt with None -> "" | Some s -> "\n" ^ indent ^ "Else\n" ^ (string_of_stmt (indent ^ "  ") s) in
      indent ^ "If (" ^ (string_of_expr c) ^ ")\n" ^ (string_of_stmt (indent ^ "  ") t) ^ else_str
  | Block stmts -> indent ^ "{\n" ^ (String.concat "\n" (List.map (string_of_stmt (indent ^ "  ")) stmts)) ^ "\n" ^ indent ^ "}"
  | Decl (t, n, i_opt) -> let init_str = match i_opt with Some e -> " = " ^ (string_of_expr e) | None -> "" in
      Printf.sprintf "%sDecl %s %s%s;" indent t n init_str
  | ArrayDecl (t, n, s) -> Printf.sprintf "%sArrayDecl %s %s[%s];" indent t n (string_of_expr s)
  | Assign (l, r) -> Printf.sprintf "%sAssign %s = %s;" indent (string_of_expr l) (string_of_expr r)
  | ExprStmt e -> Printf.sprintf "%sExprStmt %s;" indent (string_of_expr e)

let string_of_def (d: top_level_def) =
  let params_str = String.concat ", " (List.map (fun (t, n) -> t ^ " " ^ n) d.params) in
  Printf.sprintf "Function %s %s(%s)\n%s" d.ret_type d.name params_str (string_of_stmt "" d.body)

let string_of_program (p: program) = String.concat "\n\n" (List.map string_of_def p)


(* VIII. Main Driver *)

(* Helper to read all content from a channel *)
let read_all_from_channel chan =
  let buf = Buffer.create 4096 in
  try
    while true do
      Buffer.add_string buf (input_line chan);
      Buffer.add_char buf '\n'
    done;
    "" (* Unreachable *)
  with End_of_file ->
    Buffer.contents buf

(* The main compilation pipeline for normal operation (stdin to stdout) *)
let run_normal_mode () =
  let input_code = read_all_from_channel stdin in
  match parse_from_string input_code with
  | Error msg ->
      prerr_endline msg;
      exit 1
  | Ok ast ->
      let ssa_ir = Ast_to_ssa.convert_program ast in
      let optimized_ssa_ir = List.map Dce.run_on_function ssa_ir in
      match Codegen.codegen_program optimized_ssa_ir with
      | Error msg ->
          prerr_endline msg;
          exit 1
      | Ok ir_string ->
          print_endline ir_string

(* A verbose test run that prints intermediate stages for a hardcoded example *)
let run_test_mode () =
  let input_code = "
    // Swaps two integers using pointers.
    int swap(int* a, int* b) {
      int temp = *a;
      *a = *b;
      *b = temp;
      return 0;
    }

    int main() {
      int x = 10;
      int y = 20;
      swap(&x, &y);

      // Loop to sum numbers. x should now be 20.
      int i = 0;
      int sum = 0;
      for (i = 0; i < x; i = i + 1) {
        sum = sum + i;
        int dead_in_loop = 5; // Should be removed by DCE
      }

      return sum; // Should be 0+1+...+19 = 190
    }
  " in

  print_endline "--- Mini-C Compiler (Test Mode) ---";
  print_endline "Input Code:";
  print_endline "--------------------------";
  print_endline input_code;
  print_endline "--------------------------\n";

  (* --- Phase 1: Parsing --- *)
  print_endline "PHASE 1: Parsing...";
  match parse_from_string input_code with
  | Error msg ->
      print_endline ("Parsing failed: " ^ msg);
      exit 1
  | Ok ast ->
      print_endline "Successfully parsed. Generated AST:";
      print_endline (string_of_program ast);
      print_endline "\n--------------------------\n";

      (* --- Phase 2: AST to SSA Conversion --- *)
      print_endline "PHASE 2: Converting AST to SSA IR...";
      let ssa_ir = Ast_to_ssa.convert_program ast in
      print_endline "Successfully generated SSA IR:";
      print_endline (Ssa_printer.string_of_program ssa_ir);
      print_endline "\n--------------------------\n";

      (* --- Phase 3: Dead Code Elimination --- *)
      print_endline "PHASE 3: Running Dead Code Elimination...";
      let optimized_ssa_ir = List.map Dce.run_on_function ssa_ir in
      print_endline "SSA IR after DCE:";
      print_endline (Ssa_printer.string_of_program optimized_ssa_ir);
      print_endline "\n--------------------------\n";

      (* --- Phase 4: Code Generation from SSA --- *)
      print_endline "PHASE 4: Generating LLVM IR from SSA...";
      match Codegen.codegen_program optimized_ssa_ir with
      | Error msg ->
          print_endline ("Codegen failed: " ^ msg);
          exit 1
      | Ok ir_string ->
          print_endline "Successfully generated LLVM IR from optimized SSA:";
          print_endline ir_string;
          let output_filename = "output.ll" in
          (try
            let oc = open_out output_filename in
            Printf.fprintf oc "%s\n" ir_string;
            close_out oc;
            Printf.printf "\nLLVM IR also written to %s\n" output_filename
          with Sys_error err ->
            Printf.eprintf "Error writing to file %s: %s\n" output_filename err);
          ()

let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "--test" then
    run_test_mode ()
  else
    run_normal_mode ()
