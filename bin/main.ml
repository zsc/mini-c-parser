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
  | T_Int | T_Return | T_If | T_Else | T_While | T_For | T_Do
  | T_Id of string | T_Num of int
  | T_Plus | T_Minus | T_Star | T_Slash | T_Le | T_Eq | T_Ne | T_Lt | T_Gt | T_Ge
  | T_Lparen | T_Rparen | T_Assign | T_Lbrace | T_Rbrace | T_Lbracket | T_Rbracket | T_Ampersand
  | T_Comma | T_Semicolon | T_Eof

let keyword_map = [
  ("int", T_Int); ("return", T_Return); ("if", T_If); ("else", T_Else);
  ("while", T_While); ("for", T_For); ("do", T_Do)
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
  | T_Int -> "T_Int" | T_Return -> "T_Return" | T_If -> "T_If" | T_Else -> "T_Else" | T_While -> "T_While" | T_For -> "T_For" | T_Do -> "T_Do"
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
  | T_Semicolon :: rest ->
      (* Handle empty statement, e.g., for(..); or just ;; *)
      (Block [], rest)
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
  | T_Do :: rest ->
      let (body_stmt, rest1) = parse_stmt rest in
      let rest2 = expect T_While rest1 in
      let rest3 = expect T_Lparen rest2 in
      let (cond_expr, rest4) = parse_expr rest3 in
      let rest5 = expect T_Rparen rest4 in
      let rest_final = expect T_Semicolon rest5 in
      (DoWhile (body_stmt, cond_expr), rest_final)
  | T_While :: rest ->
      let rest1 = expect T_Lparen rest in
      let (cond, rest2) = parse_expr rest1 in
      let rest3 = expect T_Rparen rest2 in
      let (body, rest_final) = parse_stmt rest3 in
      (While (cond, body), rest_final)
  | T_For :: rest -> (* Desugar for loop into a while loop *)
      let rest1 = expect T_Lparen rest in
      (* Parse initializer: can be a declaration or expression stmt *)
      let (init_stmt, rest3) =
        match rest1 with
        | T_Semicolon :: r -> (Block [], r) (* Empty initializer, consume the semicolon *)
        | _ -> parse_stmt rest1 (* Non-empty: parse_stmt consumes the required semicolon *)
      in
      (* Parse condition *)
      let (cond_expr, rest4) = if List.hd rest3 = T_Semicolon then (Cst 1, rest3) (* Empty cond is true *)
                               else parse_expr rest3 in
      let rest5 = expect T_Semicolon rest4 in
      (* Parse post-loop expression *)
      let (post_stmt_opt, rest6) =
        if List.hd rest5 = T_Rparen then (None, rest5)
        else
          (* The post-loop part can be an assignment (e.g. i=i+1) or an expression (e.g. f()).
             Our AST separates these, so we can't just parse an 'expression'.
             Instead, we replicate the logic from statement parsing but without expecting a semicolon. *)
          let (lhs_expr, rest_after_lhs) = parse_expr rest5 in
          match rest_after_lhs with
          | T_Assign :: rest_assign ->
              let (rhs_expr, rest_after_rhs) = parse_expr rest_assign in
              (Some (Assign (lhs_expr, rhs_expr)), rest_after_rhs)
          | _ ->
              (Some (ExprStmt lhs_expr), rest_after_lhs)
      in
      let rest7 = expect T_Rparen rest6 in
      let (body_stmt, rest_final) = parse_stmt rest7 in
      (* Desugar: { init; while(cond) { body; post; } } *)
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
  | _ -> (* If it's not a keyword statement or declaration, it must be an expression-based one. *)
      let (lhs_expr, rest_expr) = parse_expr tokens in
      (match rest_expr with
        | T_Assign :: rest_assign ->
            let (rhs_expr, rest_rhs) = parse_expr rest_assign in
            let rest_final = expect T_Semicolon rest_rhs in
            (Assign(lhs_expr, rhs_expr), rest_final)
        | T_Semicolon :: rest_final -> (ExprStmt lhs_expr, rest_final)
        | _ -> fail_parse "Expected '=' or ';' after expression statement")

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


(* VI. Code Generation (from SSA to LLVM IR) *)
module Codegen = struct
  open Ssa
  open Ast_to_ssa

  let string_of_ssa_reg (R i) = "%r" ^ string_of_int i
  let string_of_ssa_bbid (L i) = "L" ^ string_of_int i

  let rec ll_type_of_ssa_type (typ: string) : string =
    if typ = "int" then "i32"
    else
      let len = String.length typ in
      if len > 0 && typ.[len - 1] = '*' then
        (ll_type_of_ssa_type (get_pointee_type typ)) ^ "*"
      else failwith ("Unknown SSA type for codegen: " ^ typ)

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

  let codegen_instr (reg_types: (reg, string) Hashtbl.t) (instr: instruction) : string list =
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
        let get_arg_with_type op =
          let s_op = string_of_ssa_operand op in
          let ssa_type = match op with
            | O_Cst _ -> "int" (* Constants are always int in our language *)
            | O_Reg r ->
                (try Hashtbl.find reg_types r
                 with Not_found -> failwith ("codegen: could not find type for register " ^ string_of_ssa_reg r))
            | O_Global _ -> failwith "codegen: cannot use global as function argument"
          in
          (ll_type_of_ssa_type ssa_type) ^ " " ^ s_op
        in
        let arg_strs = List.map get_arg_with_type args in
        (* The compiler currently assumes all functions return int (i32). *)
        [Printf.sprintf "  %s = call i32 @%s(%s)" dest_reg name (String.concat ", " arg_strs)]
    | D_Phi _ -> failwith "LLVM Codegen: Phi nodes not supported in this simplified compiler"
    | D_Alloca typ ->
        let ll_type = ll_type_of_ssa_type typ in
        [Printf.sprintf "  %s = alloca %s, align 4" dest_reg ll_type]
    | D_Load addr_op ->
        let res_type_str = Hashtbl.find reg_types instr.reg in
        let ll_res_type = ll_type_of_ssa_type res_type_str in
        let ll_ptr_type = ll_res_type ^ "*" in
        let s_addr = string_of_ssa_operand addr_op in
        [Printf.sprintf "  %s = load %s, %s %s, align 4" dest_reg ll_res_type ll_ptr_type s_addr]

  let codegen_side_effect (reg_types: (reg, string) Hashtbl.t) (sei: side_effect_instr) : string =
    match sei with
    | S_Store (addr_op, val_op) ->
        let s_addr = string_of_ssa_operand addr_op in
        let s_val = string_of_ssa_operand val_op in
        let val_type_str = match val_op with
          | O_Reg r -> Hashtbl.find reg_types r
          | O_Cst _ -> "int"
          | O_Global _ -> failwith "Cannot store a global function name" in
        let ll_val_type = ll_type_of_ssa_type val_type_str in
        Printf.sprintf "  store %s %s, %s* %s, align 4" ll_val_type s_val ll_val_type s_addr

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

  let codegen_bb (reg_types: (reg, string) Hashtbl.t) (bb: basic_block) : string list =
    let label = (string_of_ssa_bbid bb.id) ^ ":" in
    let ops_code = List.concat_map (function
      | I_Instr i -> codegen_instr reg_types i
      | I_Side_Effect s -> [codegen_side_effect reg_types s]
      ) bb.ops in
    let term = codegen_terminator bb.term in
    [label] @ ops_code @ term

  let codegen_func (f: func_def) : string =
    let param_strs = List.map (fun r -> (ll_type_of_ssa_type (Hashtbl.find f.reg_types r)) ^ " " ^ string_of_ssa_reg r) f.params in
    let signature = Printf.sprintf "define i32 @%s(%s) {" f.name (String.concat ", " param_strs) in
    let body_lines = List.concat_map (codegen_bb f.reg_types) f.blocks in
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
  | DoWhile (b, c) -> indent ^ "Do\n" ^ (string_of_stmt (indent ^ "  ") b) ^ "\n" ^ indent ^ "While (" ^ (string_of_expr c) ^ ");"
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

(* The main compilation pipeline. Can be run in verbose mode. *)
let process_input input_code verbose is_test =
  if verbose then (
    let mode_str = if is_test then "(Test Mode)" else "(Normal Mode)" in
    print_endline ("--- Mini-C Compiler " ^ mode_str ^ " ---");
    print_endline "Input Code:";
    print_endline "--------------------------";
    print_endline input_code;
    print_endline "--------------------------\n";
  );

  (* --- Phase 1: Parsing --- *)
  if verbose then print_endline "PHASE 1: Parsing...";
  match parse_from_string input_code with
  | Error msg ->
      prerr_endline ("Parsing failed: " ^ msg);
      exit 1
  | Ok ast ->
      if verbose then (
        print_endline "Successfully parsed. Generated AST:";
        print_endline (string_of_program ast);
        print_endline "\n--------------------------\n";
      );

      (* --- Phase 2: AST to SSA Conversion --- *)
      if verbose then print_endline "PHASE 2: Converting AST to SSA IR...";
      let ssa_ir = Ast_to_ssa.convert_program ast in
      if verbose then (
        print_endline "Successfully generated SSA IR:";
        print_endline (Ssa_printer.string_of_program ssa_ir);
        print_endline "\n--------------------------\n";
      );

      (* --- Phase 3: Dead Code Elimination --- *)
      if verbose then print_endline "PHASE 3: Running Dead Code Elimination...";
      let optimized_ssa_ir = List.map Dce.run_on_function ssa_ir in
      if verbose then (
        print_endline "SSA IR after DCE:";
        print_endline (Ssa_printer.string_of_program optimized_ssa_ir);
        print_endline "\n--------------------------\n";
      );

      (* --- Phase 4: Code Generation from SSA --- *)
      if verbose then print_endline "PHASE 4: Generating LLVM IR from SSA...";
      match Codegen.codegen_program optimized_ssa_ir with
      | Error msg ->
          prerr_endline ("Codegen failed: " ^ msg);
          exit 1
      | Ok ir_string ->
          if verbose then print_endline "Successfully generated LLVM IR from optimized SSA:";
          print_endline ir_string;
          if verbose then (
            let output_filename = "output.ll" in
            (try
              let oc = open_out output_filename in
              Printf.fprintf oc "%s\n" ir_string;
              close_out oc;
              Printf.printf "\nLLVM IR also written to %s\n" output_filename
            with Sys_error err ->
              Printf.eprintf "Error writing to file %s: %s\n" output_filename err);
          )

let () =
  let args = Array.to_list Sys.argv in
  let is_test = List.mem "--test" args in
  let is_verbose = List.mem "--verbose" args in

  let input_code =
    if is_test then "
int
main()
{
    int x;

    x = 50;
    do
        x = x - 1;
    while(x);
    return x;
}
      "
    else
      read_all_from_channel stdin
  in
  process_input input_code is_verbose is_test
