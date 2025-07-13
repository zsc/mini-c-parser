(* file: bin/main.ml *)

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
  | T_Int | T_Return | T_If | T_Else | T_Id of string | T_Num of int
  | T_Plus | T_Minus | T_Star | T_Slash | T_Le | T_Eq | T_Ne | T_Lt | T_Gt | T_Ge
  | T_Lparen | T_Rparen | T_Assign | T_Lbrace | T_Rbrace | T_Lbracket | T_Rbracket
  | T_Comma | T_Semicolon | T_Eof

let keyword_map = [ ("int", T_Int); ("return", T_Return); ("if", T_If); ("else", T_Else) ]

let token_specs = [
  (Str.regexp "[ \t\n\r]+", fun _ -> None); (Str.regexp "//[^\n]*", fun _ -> None); (Str.regexp "/\\*.*?\\*/", fun _ -> None);
  (Str.regexp "[a-zA-Z_][a-zA-Z0-9_]*", fun s -> try Some (List.assoc s keyword_map) with Not_found -> Some (T_Id s));
  (Str.regexp "[0-9]+", fun s -> Some (T_Num (int_of_string s)));
  (Str.regexp "<=", fun _ -> Some T_Le); (Str.regexp "==", fun _ -> Some T_Eq); (Str.regexp "!=", fun _ -> Some T_Ne);
  (Str.regexp ">=", fun _ -> Some T_Ge); (Str.regexp "<", fun _ -> Some T_Lt); (Str.regexp ">", fun _ -> Some T_Gt);
  (Str.regexp "+", fun _ -> Some T_Plus); (Str.regexp "-", fun _ -> Some T_Minus); (Str.regexp "=", fun _ -> Some T_Assign);
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
  | T_Int -> "T_Int" | T_Return -> "T_Return" | T_If -> "T_If" | T_Else -> "T_Else"
  | T_Id s -> Printf.sprintf "T_Id(%s)" s | T_Num n -> Printf.sprintf "T_Num(%d)" n
  | T_Plus -> "T_Plus" | T_Minus -> "T_Minus" | T_Star -> "T_Star" | T_Slash -> "T_Slash"
  | T_Le -> "T_Le" | T_Eq -> "T_Eq" | T_Ne -> "T_Ne" | T_Lt -> "T_Lt" | T_Gt -> "T_Gt" | T_Ge -> "T_Ge"
  | T_Lparen -> "T_Lparen" | T_Rparen -> "T_Rparen" | T_Assign -> "T_Assign"
  | T_Lbrace -> "T_Lbrace" | T_Rbrace -> "T_Rbrace" | T_Lbracket -> "T_Lbracket" | T_Rbracket -> "T_Rbracket"
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
  | T_Int :: T_Lbracket :: T_Rbracket :: rest -> ("int[]", rest)
  | T_Int :: rest -> ("int", rest)
  | _ -> fail_parse "Expected type name (e.g., 'int')"

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

(* IV. Code Generation (to LLVM IR as String) *)

module Codegen = struct
  (* Helper for logging *)
  let log msg = print_endline ("[Codegen] " ^ msg)

  (* --- State Management for Code Generation --- *)
  type codegen_context = {
    mutable temp_counter: int;          (* For generating unique temporary register names, e.g., %1, %2 *)
    mutable label_counter: int;         (* For generating unique label names, e.g., if.then1, if.end2 *)
    symbol_table: (string, string) Hashtbl.t; (* Maps C var names to LLVM pointer names, e.g., "n" -> "%n.addr" *)
  }

  let create_context () = {
    temp_counter = 0;
    label_counter = 0;
    symbol_table = Hashtbl.create 10;
  }

  (* Generates a new temporary register name, e.g., "%1" *)
  let new_temp ctx =
    let i = ctx.temp_counter in
    ctx.temp_counter <- i + 1;
    "%" ^ string_of_int i

  (* Generates a new label name, e.g., "if.then.1" *)
  let new_label ctx prefix =
    let i = ctx.label_counter in
    ctx.label_counter <- i + 1;
    prefix ^ "." ^ string_of_int i

  (* Maps our AST binop to LLVM instruction and comparison predicate *)
  let string_of_binop = function
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

  (* --- AST Traversal and Code Generation --- *)

  (* codegen_expr: generates instructions for an expression.
     Returns a pair: (list of instruction strings, result register/value name) *)
  let rec codegen_expr ctx (expr: expr) : string list * string =
    match expr with
    | Cst i -> ([], string_of_int i)
    | Id s ->
        log ("Generating expr: Id(" ^ s ^ ")");
        let ptr_name =
          try Hashtbl.find ctx.symbol_table s
          with Not_found -> failwith ("Codegen error: Unknown variable name: " ^ s)
        in
        let res_name = new_temp ctx in
        let instr = Printf.sprintf "  %s = load i32, i32* %s, align 4" res_name ptr_name in
        ([instr], res_name)
    | BinOp (op, e1, e2) ->
        log "Generating expr: BinOp";
        let (instrs1, res1) = codegen_expr ctx e1 in
        let (instrs2, res2) = codegen_expr ctx e2 in
        let op_str = string_of_binop op in
        let is_comparison = match op with Lt|Le|Gt|Ge|Eq|Ne -> true | _ -> false in
        if is_comparison then
          (* Comparisons produce an i1, which we must extend to i32 (0 or 1) for C semantics *)
          let i1_res = new_temp ctx in
          let cmp_instr = Printf.sprintf "  %s = %s i32 %s, %s" i1_res op_str res1 res2 in
          let res_name = new_temp ctx in
          let zext_instr = Printf.sprintf "  %s = zext i1 %s to i32" res_name i1_res in
          (instrs1 @ instrs2 @ [cmp_instr; zext_instr], res_name)
        else
          (* Arithmetic operations produce an i32 directly *)
          let res_name = new_temp ctx in
          let instr = Printf.sprintf "  %s = %s i32 %s, %s" res_name op_str res1 res2 in
          (instrs1 @ instrs2 @ [instr], res_name)
    | Call (name, args) ->
        log ("Generating expr: Call to '" ^ name ^ "'");
        let (arg_instrs, arg_ress) =
          List.fold_left (fun (acc_instrs, acc_ress) arg_expr ->
            let (instrs, res) = codegen_expr ctx arg_expr in
            (acc_instrs @ instrs, acc_ress @ [res])
          ) ([], []) args
        in
        let args_str = String.concat ", " (List.map (fun r -> "i32 " ^ r) arg_ress) in
        let res_name = new_temp ctx in
        let instr = Printf.sprintf "  %s = call i32 @%s(%s)" res_name name args_str in
        (arg_instrs @ [instr], res_name)
    | ArrayAccess (_, _) -> failwith "Array access codegen not yet implemented"

  (* Helper to check if a list of instructions is terminated by a 'ret' or 'br' *)
  let has_terminator instrs =
    match List.rev instrs with
    | [] -> false
    | last :: _ ->
        let trimmed = String.trim last in
        String.starts_with ~prefix:"ret " trimmed || String.starts_with ~prefix:"br " trimmed || String.starts_with ~prefix:"unreachable" trimmed

  (* codegen_stmt: generates a list of instruction strings for a statement. *)
  let rec codegen_stmt ctx (stmt: stmt) : string list =
    match stmt with
    | Block stmts ->
        log "Generating stmt: Block";
        List.concat_map (codegen_stmt ctx) stmts
    | ExprStmt e ->
        log "Generating stmt: ExprStmt";
        let (instrs, _) = codegen_expr ctx e in
        instrs
    | Return e ->
        log "Generating stmt: Return";
        let (instrs, res) = codegen_expr ctx e in
        instrs @ [Printf.sprintf "  ret i32 %s" res]
    | If (cond, then_s, else_s_opt) ->
        log "Generating stmt: If";
        let (cond_instrs, cond_res) = codegen_expr ctx cond in
        (* In C, any non-zero value is true. LLVM's `br` needs an `i1`. *)
        let i1_res = new_temp ctx in
        let cmp_instr = Printf.sprintf "  %s = icmp ne i32 %s, 0" i1_res cond_res in

        let then_label = new_label ctx "if.then" in
        let else_label = new_label ctx "if.else" in
        let end_label = new_label ctx "if.end" in
        let else_dest = match else_s_opt with Some _ -> else_label | None -> end_label in

        let br_instr = Printf.sprintf "  br i1 %s, label %%%s, label %%%s" i1_res then_label else_dest in

        let then_instrs = codegen_stmt ctx then_s in
        let then_block =
          (then_label ^ ":") :: then_instrs @
          (if has_terminator then_instrs then [] else [Printf.sprintf "  br label %%%s" end_label])
        in

        let else_block, needs_end_label =
          match else_s_opt with
          | Some s ->
              let else_instrs = codegen_stmt ctx s in (* This could be a single expression, no need for new variable *)
              let block = (else_label ^ ":") :: else_instrs @
                          (if has_terminator else_instrs then [] else [Printf.sprintf "  br label %%%s" end_label])
              in (block, true)
          | None -> ([], true) (* The 'false' path of the initial branch jumps to the end label, so it must be emitted. *)
        in
        let end_block = if needs_end_label then [end_label ^ ":"] else [] in

        cond_instrs @ [cmp_instr; br_instr] @ then_block @ else_block @ end_block

    (* NOTE: `alloca`s are handled in `codegen_func_def` to ensure they are in the entry block.
       This function only handles the initialization store. *)
    | Decl (_, name, init_opt) ->
        log ("Generating stmt: Decl for var '" ^ name ^ "'");
        (match init_opt with
        | Some e ->
            log (" -> Generating initializer for '" ^ name ^ "'");
            let (instrs, res) = codegen_expr ctx e in
            let ptr_name = Hashtbl.find ctx.symbol_table name in
            let store_instr = Printf.sprintf "  store i32 %s, i32* %s, align 4" res ptr_name in
            instrs @ [store_instr]
        | None -> [])
    | ArrayDecl _ -> failwith "Array declaration codegen not yet implemented"
    | Assign (lhs, rhs) ->
        log "Generating stmt: Assign";
        let ptr_name = match lhs with
          | Id s ->
              (try Hashtbl.find ctx.symbol_table s
               with Not_found -> failwith ("Undeclared variable for assignment: " ^ s))
          | _ -> failwith "LHS of assignment must be a variable"
        in
        let (rhs_instrs, rhs_res) = codegen_expr ctx rhs in
        let store_instr = Printf.sprintf "  store i32 %s, i32* %s, align 4" rhs_res ptr_name in
        rhs_instrs @ [store_instr]

  (* Traverses the AST of a function body to find all local variable declarations. *)
  let rec find_decls_in_stmt (stmt: stmt) : (string * string) list =
    match stmt with
    | Decl (typ, name, _) -> [(typ, name)]
    | ArrayDecl (typ, name, _) -> [(typ, name)]
    | If (_, then_s, else_s_opt) ->
        let then_decls = find_decls_in_stmt then_s in
        let else_decls = match else_s_opt with Some s -> find_decls_in_stmt s | None -> [] in
        then_decls @ else_decls
    | Block stmts -> List.concat_map find_decls_in_stmt stmts
    | _ -> []

  let codegen_func_def (fdef: top_level_def) : string =
    log ("--- Defining function: " ^ fdef.name ^ " ---");
    let ctx = create_context () in

    (* 1. Generate function signature *)
    let params_str =
      String.concat ", " (List.map (fun (_, n) -> "i32 %" ^ n) fdef.params) in
    let signature = Printf.sprintf "define i32 @%s(%s) {" fdef.name params_str in

    (* 2. Create entry block instructions *)
    let entry_block_label = ["entry:"] in

    (* `alloca` and `store` for parameters *)
    let param_setup_instrs =
      List.concat_map (fun (_, name) ->
        let ptr_name = "%" ^ name ^ ".addr" in
        Hashtbl.add ctx.symbol_table name ptr_name;
        [ Printf.sprintf "  %s = alloca i32, align 4" ptr_name;
          Printf.sprintf "  store i32 %%%s, i32* %s, align 4" name ptr_name ]
      ) fdef.params
    in

    (* `alloca` for all local variables found in the function body *)
    let local_decls = find_decls_in_stmt fdef.body in
    let local_allocas =
      List.map (fun (_, name) ->
        let ptr_name = "%" ^ name ^ ".addr" in
        Hashtbl.add ctx.symbol_table name ptr_name;
        Printf.sprintf "  %s = alloca i32, align 4" ptr_name
      ) local_decls
    in
    
    let initial_allocas = param_setup_instrs @ local_allocas in
    (* Jump from entry to the first real block of code *)
    let code_label = new_label ctx "code.start" in
    let entry_branch = [Printf.sprintf "  br label %%%s" code_label] in
    let first_code_block_label = [code_label ^ ":"] in

    (* 3. Generate code for the function body statements *)
    log " -> Generating function body";
    let body_instrs = codegen_stmt ctx fdef.body in

    (* Add a terminator if the function doesn't end with one *)
    let final_body =
      if has_terminator body_instrs then body_instrs
      else begin
        log " -> Block not terminated, adding unreachable.";
        body_instrs @ ["  unreachable"]
      end
    in

    (* 4. Assemble the full function string *)
    let all_lines =
      [signature]
      @ entry_block_label
      @ initial_allocas
      @ entry_branch
      @ first_code_block_label
      @ final_body
      @ ["}"]
    in
    log ("--- Finished function: " ^ fdef.name ^ " ---");
    String.concat "\n" all_lines


  let codegen_program (prog: program) : (string, string) result =
    try
        log "Starting codegen for program";
        let func_defs = List.map codegen_func_def prog in
        let full_module = String.concat "\n\n" func_defs in
        log "Codegen program finished.";
        Ok full_module
    with
    | Failure msg -> Error ("Codegen failed: " ^ msg)

end

(* V. AST Pretty Printer (for debugging) *)

let rec string_of_expr = function
  | Cst n -> string_of_int n | Id s -> s
  | BinOp (op, e1, e2) ->
      let op_str = match op with Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"
        | Le -> "<=" | Eq -> "==" | Ne -> "!=" | Lt -> "<" | Gt -> ">" | Ge -> ">=" in
      Printf.sprintf "(%s %s %s)" (string_of_expr e1) op_str (string_of_expr e2)
  | Call (n, args) -> Printf.sprintf "%s(%s)" n (String.concat ", " (List.map string_of_expr args))
  | ArrayAccess (b, i) -> Printf.sprintf "%s[%s]" (string_of_expr b) (string_of_expr i)

let rec string_of_stmt indent = function
  | Return e -> indent ^ "Return " ^ (string_of_expr e) ^ ";"
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


(* VI. Main Driver *)
let () =
  let input_code = "
    int fac(int n) {
      if (n <= 1) {
        return 1;
      }
      return n * fac(n-1);
    }

    int main() {
      int result = fac(4);
      return result;
    }
  " in

  print_endline "--- Mini-C Compiler ---";
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

      (* --- Phase 2: Code Generation --- *)
      print_endline "PHASE 2: Generating LLVM IR...";
      match Codegen.codegen_program ast with
      | Error msg ->
          print_endline ("Codegen failed: " ^ msg);
          exit 1
      | Ok ir_string ->
          (* --- Phase 3: Output --- *)
          print_endline "Successfully generated LLVM IR:";
          print_endline ir_string;

          (* Write to a file *)
          let output_filename = "output.ll" in
          (try
            let oc = open_out output_filename in
            Printf.fprintf oc "%s\n" ir_string;
            close_out oc;
            Printf.printf "\nLLVM IR also written to %s\n" output_filename
          with Sys_error err ->
            Printf.eprintf "Error writing to file %s: %s\n" output_filename err);
