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


(* Tokenizer (Lexer) *)

type token =
  | T_Int | T_Char | T_Float | T_Double | T_Void | T_Struct | T_Union | T_Enum
  | T_Return | T_If | T_Else | T_While | T_For | T_Do
  | T_Id of string | T_Num of int | T_FNum of float | T_String of string | T_Char_Lit of char
  | T_Plus | T_Minus | T_Star | T_Slash | T_Percent
  | T_Le | T_Eq | T_Ne | T_Lt | T_Gt | T_Ge
  | T_Lparen | T_Rparen | T_Assign | T_Lbrace | T_Rbrace | T_Lbracket | T_Rbracket | T_Ampersand
  | T_Pipe | T_Caret | T_Comma | T_Semicolon | T_Dot | T_Arrow | T_Eof

let keyword_map = [
  ("int", T_Int); ("char", T_Char); ("float", T_Float); ("double", T_Double); ("void", T_Void);
  ("struct", T_Struct); ("union", T_Union); ("enum", T_Enum);
  ("return", T_Return); ("if", T_If); ("else", T_Else);
  ("while", T_While); ("for", T_For); ("do", T_Do)
]

(* Helper to unescape C-style string and char literals *)
let unescape s =
  let n = String.length s in
  let buf = Buffer.create n in
  let i = ref 0 in
  while !i < n do
    if s.[!i] = '\\' then (
      i := !i + 1;
      if !i < n then
        let c = s.[!i] in
        i := !i + 1;
        match c with
        | 'n' -> Buffer.add_char buf '\n'
        | 't' -> Buffer.add_char buf '\t'
        | 'r' -> Buffer.add_char buf '\r'
        | '\\' -> Buffer.add_char buf '\\'
        | '\'' -> Buffer.add_char buf '\''
        | '"' -> Buffer.add_char buf '\"'
        | '0' .. '7' as c1 ->
          let v = ref (Char.code c1 - Char.code '0') in
          if !i < n && s.[!i] >= '0' && s.[!i] <= '7' then (
            v := !v * 8 + (Char.code s.[!i] - Char.code '0');
            i := !i + 1;
            if !i < n && s.[!i] >= '0' && s.[!i] <= '7' then (
              v := !v * 8 + (Char.code s.[!i] - Char.code '0');
              i := !i + 1;
            )
          );
          Buffer.add_char buf (Char.chr !v)
        | 'x' ->
          let v = ref 0 in
          let has_digit = ref false in
          while !i < n && (let c_hex = s.[!i] in ('0' <= c_hex && c_hex <= '9') || ('a' <= c_hex && c_hex <= 'f') || ('A' <= c_hex && c_hex <= 'F')) do
            has_digit := true;
            let digit = s.[!i] in
            let d_val = if '0' <= digit && digit <= '9' then Char.code digit - Char.code '0'
                        else if 'a' <= digit && digit <= 'f' then Char.code digit - Char.code 'a' + 10
                        else Char.code digit - Char.code 'A' + 10 in
            v := !v * 16 + d_val;
            i := !i + 1
          done;
          if not !has_digit then failwith "Invalid hex escape: '\\x' with no digits";
          Buffer.add_char buf (Char.chr !v)
        | c -> Buffer.add_char buf c (* Unknown escape sequence, just pass char *)
      else
        Buffer.add_char buf '\\'
    ) else (
      Buffer.add_char buf s.[!i];
      i := !i + 1
    )
  done;
  Buffer.contents buf

let token_specs = [
  (Str.regexp "[ \t\n\r]+", fun _ -> None); (Str.regexp "#[^\n]*", fun _ -> None);
  (Str.regexp "\"[^\"\\\\]*\\(\\\\.[^\"\\\\]*\\)*\"", fun s -> Some (T_String (unescape (String.sub s 1 (String.length s - 2)))));
  (Str.regexp "'\\([^'\\\\]\\|\\\\.\\)+'", fun s -> Some (T_Char_Lit ((unescape (String.sub s 1 (String.length s - 2))).[0])));
  (Str.regexp "[a-zA-Z_][a-zA-Z0-9_]*", fun s -> try Some (List.assoc s keyword_map) with Not_found -> Some (T_Id s));
  (Str.regexp "[0-9]+\\.[0-9]*\\([eE][-+]?[0-9]+\\)?", fun s -> Some (T_FNum (float_of_string s)));
  (Str.regexp "[0-9]+", fun s -> Some (T_Num (int_of_string s)));
  (Str.regexp "<=", fun _ -> Some T_Le); (Str.regexp "==", fun _ -> Some T_Eq); (Str.regexp "!=", fun _ -> Some T_Ne);
  (Str.regexp ">=", fun _ -> Some T_Ge); (Str.regexp "<", fun _ -> Some T_Lt); (Str.regexp ">", fun _ -> Some T_Gt);
  (Str.regexp "[+]", fun _ -> Some T_Plus); (Str.regexp "-", fun _ -> Some T_Minus); (Str.regexp "&", fun _ -> Some T_Ampersand); (Str.regexp "=", fun _ -> Some T_Assign);
  (Str.regexp "->", fun _ -> Some T_Arrow);
  (Str.regexp "[*]", fun _ -> Some T_Star); (Str.regexp "/", fun _ -> Some T_Slash); (Str.regexp "[%]", fun _ -> Some T_Percent);
  (Str.regexp "[|]", fun _ -> Some T_Pipe); (Str.regexp "[\\^]", fun _ -> Some T_Caret);
  (Str.regexp "[(]", fun _ -> Some T_Lparen); (Str.regexp "[)]", fun _ -> Some T_Rparen);
  (Str.regexp "[{]", fun _ -> Some T_Lbrace); (Str.regexp "[}]", fun _ -> Some T_Rbrace);
  (Str.regexp "\\[", fun _ -> Some T_Lbracket); (Str.regexp "\\]", fun _ -> Some T_Rbracket);
  (Str.regexp ",", fun _ -> Some T_Comma); (Str.regexp ";", fun _ -> Some T_Semicolon);
  (Str.regexp "\\.", fun _ -> Some T_Dot);
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

(* Parser *)

exception Parser_error of string

let fail_parse msg = raise (Parser_error msg)

let string_of_token = function
  | T_Int -> "T_Int" | T_Char -> "T_Char" | T_Float -> "T_Float" | T_Double -> "T_Double" | T_Void -> "T_Void" | T_Struct -> "T_Struct" | T_Union -> "T_Union" | T_Enum -> "T_Enum"
  | T_Return -> "T_Return" | T_If -> "T_If" | T_Else -> "T_Else" | T_While -> "T_While" | T_For -> "T_For" | T_Do -> "T_Do"
  | T_String s -> Printf.sprintf "T_String(\"%s\")" (String.escaped s) | T_Char_Lit c -> Printf.sprintf "T_Char_Lit('%c')" c
  | T_Id s -> Printf.sprintf "T_Id(%s)" s | T_Num n -> Printf.sprintf "T_Num(%d)" n | T_FNum f -> Printf.sprintf "T_FNum(%f)" f
  | T_Plus -> "T_Plus" | T_Minus -> "T_Minus" | T_Star -> "T_Star" | T_Slash -> "T_Slash" | T_Percent -> "T_Percent"
  | T_Le -> "T_Le" | T_Eq -> "T_Eq" | T_Ne -> "T_Ne" | T_Lt -> "T_Lt" | T_Gt -> "T_Gt" | T_Ge -> "T_Ge"
  | T_Lparen -> "T_Lparen" | T_Rparen -> "T_Rparen" | T_Assign -> "T_Assign"
  | T_Lbrace -> "T_Lbrace" | T_Rbrace -> "T_Rbrace" | T_Lbracket -> "T_Lbracket" | T_Rbracket -> "T_Rbracket" | T_Dot -> "T_Dot" | T_Arrow -> "T_Arrow"
  | T_Ampersand -> "T_Ampersand"
  | T_Pipe -> "T_Pipe" | T_Caret -> "T_Caret" | T_Comma -> "T_Comma" | T_Semicolon -> "T_Semicolon" | T_Eof -> "T_Eof"

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
  match tokens with
  | T_Struct :: _ -> parse_struct_union_def true tokens
  | T_Union :: _ -> parse_struct_union_def false tokens
  | T_Enum :: _ -> let (def, r) = parse_enum_def tokens in (GEnumDef def, r)
  | _ -> parse_var_or_func_def tokens

and parse_var_or_func_def tokens =
  let (base_type, rest1) = parse_c_type tokens in
  let name, rest2 = match rest1 with T_Id s :: rest -> s, rest | _ -> fail_parse "Expected identifier in top-level definition" in
  match rest2 with
  | T_Lparen :: _ -> (* Function definition *)
      let rest3 = expect T_Lparen rest2 in
      let params, rest4 = parse_params rest3 in
      let rest5 = expect T_Rparen rest4 in
      let body, rest6 = parse_stmt rest5 in
      (GFunc { ret_type = base_type; name; params; body }, rest6)
  | T_Lbracket :: r -> (* Global array declaration *)
      let (size_expr, r') = parse_expr r in
      let r'' = expect T_Rbracket r' in
      let r_final = expect T_Semicolon r'' in
      (GArray (base_type, name, size_expr), r_final)
  | T_Assign :: r -> (* Global variable with initializer *)
      let (init_expr, r') = parse_expr r in
      let r_final = expect T_Semicolon r' in
      (GVar (base_type, name, Some init_expr), r_final)
  | T_Semicolon :: r_final -> (* Global variable without initializer *)
      (GVar (base_type, name, None), r_final)
  | _ -> fail_parse "Malformed top-level definition: expected '(', '[', '=', or ';'"

and parse_c_type tokens =
  let base_type, rest = match tokens with
    | T_Void   :: r -> (TVoid, r)
    | T_Char   :: r -> (TChar, r)
    | T_Int    :: r -> (TInt, r)
    | T_Float  :: r -> (TFloat, r)
    | T_Double :: r -> (TDouble, r)
    | T_Struct :: T_Id s :: r -> (TStruct s, r)
    | T_Union :: T_Id s :: r -> (TUnion s, r)
    | T_Enum :: T_Id s :: r -> (TEnum s, r)
    | _ -> fail_parse "Expected a type keyword (int, char, void, etc.)"
  in
  let rec parse_pointers t toks =
    match toks with
    | T_Star :: r -> parse_pointers (TPtr t) r
    | _ -> (t, toks)
  in
  parse_pointers base_type rest

and parse_struct_union_def is_struct tokens =
  let _, rest0 = if is_struct then T_Struct, List.tl tokens else T_Union, List.tl tokens in
  let name, rest1 = match rest0 with T_Id s :: r -> s, r | _ -> fail_parse ("Expected " ^ (if is_struct then "struct" else "union") ^ " name") in
  let rest2 = expect T_Lbrace rest1 in
  let rec parse_members acc toks =
    match toks with
    | T_Rbrace :: _ -> (List.rev acc, toks)
    | _ ->
        let (mem_type, r1) = parse_c_type toks in
        let mem_name, r2 = match r1 with T_Id s :: r -> s,r | _ -> fail_parse "Expected member name" in
        let r3 = expect T_Semicolon r2 in
        parse_members ((mem_type, mem_name) :: acc) r3
  in
  let members, rest3 = parse_members [] rest2 in
  let rest4 = expect T_Rbrace rest3 in
  let rest_final = expect T_Semicolon rest4 in
  if is_struct then (GStructDef { s_name = name; s_members = members }, rest_final)
  else (GUnionDef { u_name = name; u_members = members }, rest_final)

and parse_enum_def tokens =
  let rest0 = expect T_Enum tokens in
  let name_opt, rest1 = match rest0 with T_Id s :: r -> (Some s, r) | _ -> (None, rest0) in
  let rest2 = expect T_Lbrace rest1 in
  let rec parse_members acc toks =
    match toks with
    | T_Rbrace :: _ -> (List.rev acc, toks)
    | T_Id s :: r ->
        let (val_opt, r') = match r with
          | T_Assign :: r' -> let (e, r'') = parse_expr r' in (Some e, r'')
          | _ -> (None, r)
        in
        let new_acc = (s, val_opt) :: acc in
        (match r' with
         | T_Comma :: r''' -> parse_members new_acc r'''
         | _ -> (List.rev new_acc, r'))
    | _ -> fail_parse "Malformed enum definition"
  in
  let members, rest3 = parse_members [] rest2 in
  let rest4 = expect T_Rbrace rest3 in
  let rest_final = expect T_Semicolon rest4 in
  ({ e_name = name_opt; e_members = members }, rest_final)

and parse_params tokens = match tokens with
  | T_Rparen :: _ -> ([], tokens)
  | _ ->
      let rec loop acc tokens =
        let (param_type, rest1) = parse_c_type tokens in
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
      let (cond_expr, rest4) = if List.hd rest3 = T_Semicolon then (CstI 1, rest3) (* Empty cond is true *)
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
  | T_Int :: _ | T_Char :: _ | T_Float :: _ | T_Double :: _ | T_Void :: _ ->
      let (decl_type, rest_type) = parse_c_type tokens in
      let name, rest_name = match rest_type with T_Id s :: r -> s, r | _ -> fail_parse ("Expected identifier in declaration, got " ^ (string_of_token (List.hd rest_type))) in
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
  | T_Struct :: _ | T_Union :: _ | T_Enum :: _ ->
      (* Local type definitions not supported, treat as variable declaration *)
      parse_stmt (T_Int :: (List.tl tokens)) (* HACK: Re-parse as int for simplicity *)
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
and parse_assign_expr tokens = parse_bitwise_or_expr tokens
and parse_bitwise_or_expr tokens =
  let rec loop lhs toks = match toks with
    | T_Pipe :: r -> let (rhs, r') = parse_bitwise_xor_expr r in loop (BinOp (BitOr, lhs, rhs)) r'
    | _ -> (lhs, toks)
  in let (lhs, r) = parse_bitwise_xor_expr tokens in loop lhs r
and parse_bitwise_xor_expr tokens =
  let rec loop lhs toks = match toks with
    | T_Caret :: r -> let (rhs, r') = parse_bitwise_and_expr r in loop (BinOp (BitXor, lhs, rhs)) r'
    | _ -> (lhs, toks)
  in let (lhs, r) = parse_bitwise_and_expr tokens in loop lhs r
and parse_bitwise_and_expr tokens =
  let rec loop lhs toks = match toks with
    | T_Ampersand :: r -> let (rhs, r') = parse_equality_expr r in loop (BinOp (BitAnd, lhs, rhs)) r'
    | _ -> (lhs, toks)
  in let (lhs, r) = parse_equality_expr tokens in loop lhs r
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
    | T_Percent :: r -> let (rhs, r') = parse_unary_expr r in loop (BinOp (Mod, lhs, rhs)) r'
    | _ -> (lhs, toks)
  in let (lhs, r) = parse_unary_expr tokens in loop lhs r
and parse_unary_expr tokens = match tokens with
  | T_Minus :: r -> let (e, r') = parse_unary_expr r in (BinOp (Sub, CstI 0, e), r')
  | T_Plus :: r -> parse_unary_expr r
  | T_Ampersand :: r -> let (e, r') = parse_unary_expr r in (AddrOf e, r') (* Must be parse_unary to handle &*p *)
  | T_Star :: r -> let (e, r') = parse_unary_expr r in (Deref e, r')
  | _ -> parse_postfix_expr tokens
and parse_postfix_expr tokens =
  let (base, rest) = parse_primary_expr tokens in
  let rec loop base_expr tokens =
    match tokens with
    | T_Lparen :: _ -> (* Function call *)
        (* Note: this grammar doesn't support pointer-to-function calls like ( *p)(); only direct calls f(). *)
        let func_name = match base_expr with Id s -> s | _ -> fail_parse "Function name must be an identifier" in
        let rest1 = expect T_Lparen tokens in
        let (args, rest2) = parse_args rest1 in
        let rest3 = expect T_Rparen rest2 in
        loop (Call (func_name, args)) rest3
    | T_Lbracket :: rest -> (* Array access *)
        let (index_expr, rest') = parse_expr rest in
        let rest'' = expect T_Rbracket rest' in
        loop (ArrayAccess (base_expr, index_expr)) rest''
    | T_Dot :: T_Id field :: rest -> (* Member access s.f *)
        loop (MemberAccess (base_expr, field)) rest
    | T_Arrow :: T_Id field :: rest -> (* Pointer member access p->f *)
        loop (PtrMemberAccess (base_expr, field)) rest
    | _ -> (base_expr, tokens)
  in loop base rest
and parse_primary_expr tokens = match tokens with
  | T_String s :: rest ->
      let rec concat_strings acc toks = match toks with
        | T_String s' :: rest' -> concat_strings (acc ^ s') rest'
        | _ -> (CstS acc, toks)
      in concat_strings s rest
  | T_Char_Lit c :: rest -> (CstI (Char.code c), rest)
  | T_Num n :: rest -> (CstI n, rest)
  | T_FNum f :: rest -> (CstF f, rest)
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


(* Code Generation (from SSA to LLVM IR) *)
module Codegen = struct
  open Ssa
  open Ast
  open Ast_to_ssa

  let string_of_ssa_reg (R i) = "%r" ^ string_of_int i
  let string_of_ssa_bbid (L i) = "L" ^ string_of_int i

  let rec ll_type_of_c_type (typ: c_type) : string =
    match typ with
    | TVoid -> "void"
    | TChar -> "i8"
    | TInt -> "i32"
    | TFloat -> "float"
    | TDouble -> "double"
    | TPtr t -> (ll_type_of_c_type t) ^ "*"
    | TArray (t, _) -> (ll_type_of_c_type t) ^ "*"
    | TStruct s -> "%struct." ^ s
    | TUnion u -> Ast_to_ssa.((Hashtbl.find union_env u).u_ll_type)
    | TEnum _ -> "i32"

  let string_of_ssa_operand (op: operand) : string =
    match op with
    | O_CstI i -> string_of_int i
    | O_CstF f ->
        let s = Printf.sprintf "%f" f in
        if not (String.contains s '.') then s ^ ".0" else s
    | O_Reg r -> string_of_ssa_reg r
    | O_Global s -> "@" ^ s

  let ll_op_for_type (is_float: bool) (op: Ast.binop) =
    match op, is_float with
    | Add, false -> "add nsw" | Add, true -> "fadd"
    | Sub, false -> "sub nsw" | Sub, true -> "fsub"
    | Mul, false -> "mul nsw" | Mul, true -> "fmul"
    | Div, false -> "sdiv"    | Div, true -> "fdiv"
    | Mod, false -> "srem"    | Mod, true -> "frem"
    | Lt,  false -> "icmp slt" | Lt,  true -> "fcmp olt"
    | Le,  false -> "icmp sle" | Le,  true -> "fcmp ole"
    | Gt,  false -> "icmp sgt" | Gt,  true -> "fcmp ogt"
    | Ge,  false -> "icmp sge" | Ge,  true -> "fcmp oge"
    | Eq,  false -> "icmp eq"  | Eq,  true -> "fcmp oeq"
    | Ne,  false -> "icmp ne"  | Ne,  true -> "fcmp one"
    | BitAnd, false -> "and"
    | BitOr, false -> "or"
    | BitXor, false -> "xor"
    | _, true -> failwith "Unsupported float operation"

  let codegen_instr (func_reg_types: (reg, c_type) Hashtbl.t) (instr: instruction) : string list =
    let dest_reg = string_of_ssa_reg instr.reg in
    let get_op_type op = match op with
      | O_Reg r  -> Hashtbl.find func_reg_types r
      | O_CstI _ -> TInt
      | O_CstF _ -> TDouble
      | O_Global s ->
        if String.starts_with ~prefix:".str." s then TPtr TChar
        else failwith ("Codegen: Cannot determine type of global " ^ s)
    in
    match instr.def with
    | D_BinOp (op, o1, o2) ->
        let op_type = get_op_type o1 in
        let is_float = match op_type with TFloat | TDouble -> true | _ -> false in
        let op_str = ll_op_for_type is_float op in
        let s_op1 = string_of_ssa_operand o1 in
        let s_op2 = string_of_ssa_operand o2 in
        let ll_type = ll_type_of_c_type op_type in
        let is_comparison = match op with Lt|Le|Gt|Ge|Eq|Ne -> true | _ -> false in
        if is_comparison then
          let i1_res = dest_reg ^ ".i1" in
          let cmp_instr = Printf.sprintf "  %s = %s %s %s, %s" i1_res op_str ll_type s_op1 s_op2 in
          let zext_instr = Printf.sprintf "  %s = zext i1 %s to i32" dest_reg i1_res in (* Result of comparison is always i32 0 or 1 *)
          [cmp_instr; zext_instr]
        else
          [Printf.sprintf "  %s = %s %s %s, %s" dest_reg op_str ll_type s_op1 s_op2]
    | D_Call (name, args) ->
        let get_arg_with_type op =
          let s_op = string_of_ssa_operand op in
          let c_type = get_op_type op in
          (ll_type_of_c_type c_type) ^ " " ^ s_op
        in
        let arg_strs = List.map get_arg_with_type args in
        let ret_type = Hashtbl.find func_reg_types instr.reg in
        let ll_ret_type = ll_type_of_c_type ret_type in
        if ret_type = TVoid then
          [Printf.sprintf "  call void @%s(%s)" name (String.concat ", " arg_strs)]
        else
          [Printf.sprintf "  %s = call %s @%s(%s)" dest_reg ll_ret_type name (String.concat ", " arg_strs)]
    | D_Phi _ -> failwith "LLVM Codegen: Phi nodes not supported in this simplified compiler"
    | D_Alloca typ ->
        [Printf.sprintf "  %s = alloca %s, align 4" dest_reg typ] (* Type is already stringified to LLVM *)
    | D_ArrayAlloca (typ, size_op) -> (* Note: this is for local arrays on the stack *)
        let s_size = string_of_ssa_operand size_op in
        [Printf.sprintf "  %s = alloca %s, i32 %s, align 4" dest_reg typ s_size]
    | D_SIToFP op ->
        let src_type = get_op_type op in
        let dest_type = Hashtbl.find func_reg_types instr.reg in
        let ll_src_type = ll_type_of_c_type src_type in
        let ll_dest_type = ll_type_of_c_type dest_type in
        [Printf.sprintf "  %s = sitofp %s %s to %s" dest_reg ll_src_type (string_of_ssa_operand op) ll_dest_type]
    | D_GetElementPtr (base_op, index_ops) ->
        let ptr_c_type = get_op_type base_op in
        let pointee_c_type = get_pointee_type ptr_c_type in
        let ll_pointee_type = ll_type_of_c_type pointee_c_type in
        let ll_ptr_type = ll_type_of_c_type ptr_c_type in
        let s_base = string_of_ssa_operand base_op in
        let s_indices = List.map (fun op -> "i32 " ^ string_of_ssa_operand op) index_ops in
        [Printf.sprintf "  %s = getelementptr inbounds %s, %s %s, %s" dest_reg ll_pointee_type ll_ptr_type s_base (String.concat ", " s_indices)]
    | D_Bitcast op ->
        [Printf.sprintf "  %s = bitcast %s %s to %s" dest_reg (ll_type_of_c_type (get_op_type op)) (string_of_ssa_operand op) (ll_type_of_c_type (Hashtbl.find func_reg_types instr.reg))]
    | D_FPToSI op ->
        let src_type = get_op_type op in
        let dest_type = Hashtbl.find func_reg_types instr.reg in
        let ll_src_type = ll_type_of_c_type src_type in
        let ll_dest_type = ll_type_of_c_type dest_type in
        [Printf.sprintf "  %s = fptosi %s %s to %s" dest_reg ll_src_type (string_of_ssa_operand op) ll_dest_type]
    | D_Load addr_op ->
        let res_c_type = Hashtbl.find func_reg_types instr.reg in
        let ll_res_type = ll_type_of_c_type res_c_type in
        let ll_ptr_type = ll_res_type ^ "*" in
        let s_addr = string_of_ssa_operand addr_op in
        [Printf.sprintf "  %s = load %s, %s %s, align 4" dest_reg ll_res_type ll_ptr_type s_addr]

  let codegen_side_effect (func_reg_types: (reg, c_type) Hashtbl.t) (sei: side_effect_instr) : string =
    let get_op_type op = match op with
      | O_Reg r  -> Hashtbl.find func_reg_types r
      | O_CstI _ -> TInt
      | O_CstF _ -> TDouble
      | O_Global s ->
        if String.starts_with ~prefix:".str." s then TPtr TChar
        else failwith ("Codegen: Cannot determine type of global " ^ s)
    in
    match sei with
    | S_Store (addr_op, val_op) ->
        let s_addr = string_of_ssa_operand addr_op in
        let s_val = string_of_ssa_operand val_op in
        let val_c_type = get_op_type val_op in
        let ll_val_type = ll_type_of_c_type val_c_type in
        Printf.sprintf "  store %s %s, %s* %s, align 4" ll_val_type s_val ll_val_type s_addr

  let codegen_terminator (func_ret_type: c_type) (term: terminator) : string list =
    match term with
    | T_Ret op ->
        if func_ret_type = TVoid then ["  ret void"]
        else
          let ll_ret_type = ll_type_of_c_type func_ret_type in
          [Printf.sprintf "  ret %s %s" ll_ret_type (string_of_ssa_operand op)]
    | T_Br bbid -> [Printf.sprintf "  br label %%%s" (string_of_ssa_bbid bbid)]
    | T_CBr (cond_op, ltrue, lfalse) ->
        let s_cond = string_of_ssa_operand cond_op in
        let cond_type = "i32" in (* Assume all conditions are i32 for now *)
        let i1_res_for_br = "%cond_i1_" ^ (string_of_ssa_bbid ltrue) in (* Unique name *)
        let cmp_instr = Printf.sprintf "  %s = icmp ne %s %s, 0" i1_res_for_br cond_type s_cond in
        let br_instr = Printf.sprintf "  br i1 %s, label %%%s, label %%%s" i1_res_for_br (string_of_ssa_bbid ltrue) (string_of_ssa_bbid lfalse) in
        [cmp_instr; br_instr]

  let codegen_bb (f: Ssa.func_def) (func_ret_type: c_type) (bb: basic_block) : string list =
    let label = (string_of_ssa_bbid bb.id) ^ ":" in
    let ops_code = List.concat_map (function
      | I_Instr i -> codegen_instr f.reg_types i
      | I_Side_Effect s -> [codegen_side_effect f.reg_types s]
      ) bb.ops in
    let term = codegen_terminator func_ret_type bb.term in
    [label] @ ops_code @ term

  let codegen_func (f: Ssa.func_def) : string =
    let func_info = Hashtbl.find Ast_to_ssa.func_return_types f.name in
    let param_strs = List.map (fun r -> (ll_type_of_c_type (Hashtbl.find f.reg_types r)) ^ " " ^ string_of_ssa_reg r) f.params in
    let signature = Printf.sprintf "define %s @%s(%s) {" (ll_type_of_c_type func_info.ret_type) f.name (String.concat ", " param_strs) in
    let body_lines = List.concat_map (codegen_bb f func_info.ret_type) f.blocks in
    String.concat "\n" ([signature] @ body_lines @ ["}"])

  let codegen_program (globals: Ast.global_def list) (prog: Ssa.program) : (string, string) result =
    try
        let llvm_escape_string s =
          let buf = Buffer.create (String.length s * 2) in
          String.iter (fun c ->
            let code = Char.code c in
            if code >= 32 && code <= 126 && c <> '"' && c <> '\\' then
              Buffer.add_char buf c
            else
              Printf.bprintf buf "\\%02X" code
          ) s;
          Buffer.contents buf
        in

        let type_defs =
          let structs = Hashtbl.fold (fun name info acc ->
            let member_types = info.s_members |> Hashtbl.to_seq_values |> List.of_seq |> List.sort (fun f1 f2 -> compare f1.f_index f2.f_index) |> List.map (fun f -> ll_type_of_c_type f.f_type) in
            (Printf.sprintf "%%struct.%s = type { %s }" name (String.concat ", " member_types)) :: acc
          ) Ast_to_ssa.struct_env [] in
          let unions = Hashtbl.fold (fun name info acc ->
            (Printf.sprintf "%%union.%s = type { %s }" name info.u_ll_type) :: acc
          ) Ast_to_ssa.union_env [] in
          structs @ unions
        in

        let global_var_defs = List.filter_map (function
            | GVar (typ, name, init_opt) ->
                let ll_type = ll_type_of_c_type typ in
                let (linkage, init_str) = match init_opt with
                  | Some (CstI i) -> ("global", string_of_int i)
                  | Some (CstF f) -> ("global", string_of_float f)
                  | _ -> ("common global", "0")
                in
                Some (Printf.sprintf "@%s = %s %s %s, align 4" name linkage ll_type init_str)
            | GArray (typ, name, size_expr) ->
                let ll_elem_type = ll_type_of_c_type typ in
                let size = match size_expr with CstI n -> n | _ -> failwith "Codegen: Global array size must be a constant integer" in
                Some (Printf.sprintf "@%s = common global [%d x %s] zeroinitializer, align 16" name size ll_elem_type)
            | GFunc _ | GStructDef _ | GUnionDef _ | GEnumDef _ -> None
          ) globals
        in

        let string_lits =
          Hashtbl.fold (fun str_val label acc ->
            let escaped_str = llvm_escape_string (str_val ^ "\000") in
            let len = String.length str_val + 1 in
            let def = Printf.sprintf "@%s = private unnamed_addr constant [%d x i8] c\"%s\", align 1" label len escaped_str in
            def :: acc
          ) Ast_to_ssa.global_strings []
        in
        let global_defs = type_defs @ global_var_defs @ string_lits in
        let func_defs = List.map codegen_func prog in
        let full_module = String.concat "\n" global_defs ^ "\n\n" ^ String.concat "\n\n" func_defs in
        Ok full_module
    with
    | Failure msg -> Error ("Codegen failed: " ^ msg)
end

(* AST Pretty Printer (for debugging) *)
let rec string_of_c_type = function
  | TVoid -> "void" | TChar -> "char" | TInt -> "int"
  | TFloat -> "float" | TDouble -> "double"
  | TStruct s -> "struct " ^ s | TUnion u -> "union " ^ u | TEnum e -> "enum " ^ (match e with "" -> "?" | _ -> e)
  | TPtr t -> (string_of_c_type t) ^ "*"
  | TArray (t, n) -> Printf.sprintf "%s[%d]" (string_of_c_type t) n

let rec string_of_expr = function
  | CstI n -> string_of_int n
  | CstF f -> string_of_float f
  | CstS s -> "\"" ^ (String.escaped s) ^ "\""
  | Id s -> s
  | BinOp (op, e1, e2) ->
      let op_str = match op with Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
        | Le -> "<=" | Eq -> "==" | Ne -> "!=" | Lt -> "<" | Gt -> ">" | Ge -> ">="
        | BitAnd -> "&" | BitOr -> "|" | BitXor -> "^" in
      Printf.sprintf "(%s %s %s)" (string_of_expr e1) op_str (string_of_expr e2)
  | Call (n, args) -> Printf.sprintf "%s(%s)" n (String.concat ", " (List.map string_of_expr args))
  | AddrOf e -> "&(" ^ (string_of_expr e) ^ ")"
  | Deref e -> "*(" ^ (string_of_expr e) ^ ")"
  | MemberAccess (b, f) -> Printf.sprintf "%s.%s" (string_of_expr b) f
  | PtrMemberAccess (b, f) -> Printf.sprintf "%s->%s" (string_of_expr b) f
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
      Printf.sprintf "%sDecl %s %s%s;" indent (string_of_c_type t) n init_str
  | ArrayDecl (t, n, s) -> Printf.sprintf "%sArrayDecl %s %s[%s];" indent (string_of_c_type t) n (string_of_expr s)
  | Assign (l, r) -> Printf.sprintf "%sAssign %s = %s;" indent (string_of_expr l) (string_of_expr r)
  | ExprStmt e -> Printf.sprintf "%sExprStmt %s;" indent (string_of_expr e)

let string_of_global_def = function
  | GFunc f ->
      let params_str = String.concat ", " (List.map (fun (t, n) -> (string_of_c_type t) ^ " " ^ n) f.params) in
      Printf.sprintf "Function %s %s(%s)\n%s" (string_of_c_type f.ret_type) f.name params_str (string_of_stmt "" f.body)
  | GVar (t, n, e_opt) ->
      let init_str = match e_opt with Some e -> " = " ^ (string_of_expr e) | None -> "" in
      Printf.sprintf "Global Var: %s %s%s;" (string_of_c_type t) n init_str
  | GStructDef s ->
      let members_str = String.concat "; " (List.map (fun (t, n) -> (string_of_c_type t) ^ " " ^ n) s.s_members) in
      Printf.sprintf "struct %s { %s; };" s.s_name members_str
  | GUnionDef u ->
      let members_str = String.concat "; " (List.map (fun (t, n) -> (string_of_c_type t) ^ " " ^ n) u.u_members) in
      Printf.sprintf "union %s { %s; };" u.u_name members_str
  | GEnumDef e ->
      let members_str = String.concat ", " (List.map (fun (n, e_opt) -> n ^ (match e_opt with Some e -> " = " ^ string_of_expr e | None -> "")) e.e_members) in
      Printf.sprintf "enum %s { %s };" (match e.e_name with Some n -> n | None -> "") members_str
  | GArray (t, n, s) ->
      Printf.sprintf "Global Array: %s %s[%s];" (string_of_c_type t) n (string_of_expr s)

let string_of_program (p: program) = String.concat "\n\n" (List.map string_of_global_def p)

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

(* Helper to run cpp for preprocessing *)
let preprocess_with_cpp code =
  try
    let in_filename = Filename.temp_file "minic_in_" ".c" in
    let out = open_out in_filename in
    output_string out code;
    close_out out;

    let cpp_command = Printf.sprintf "cpp %s" in_filename in
    let ic = Unix.open_process_in cpp_command in
    let preprocessed_code = read_all_from_channel ic in
    let status = Unix.close_process_in ic in
    Sys.remove in_filename;

    match status with
    | WEXITED 0 -> Ok preprocessed_code
    | WEXITED n -> Error (Printf.sprintf "cpp failed with exit code %d" n)
    | WSIGNALED n -> Error (Printf.sprintf "cpp killed by signal %d" n)
    | WSTOPPED n -> Error (Printf.sprintf "cpp stopped by signal %d" n)
  with
  | e -> Error (Printexc.to_string e)


(* Main Driver *)

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

  (* --- Phase 0: Preprocessing --- *)
  let preprocessed_code =
    if verbose then print_endline "PHASE 0: Preprocessing with cpp...";
    match preprocess_with_cpp input_code with
    | Ok code ->
        if verbose then (
          print_endline "Successfully preprocessed. Code after cpp:";
          print_endline "--------------------------";
          print_endline code;
          print_endline "--------------------------\n";
        );
        code
    | Error msg ->
        prerr_endline ("Preprocessing failed: " ^ msg);
        exit 1
  in
  (* --- Phase 1: Parsing --- *)
  if verbose then print_endline "PHASE 1: Parsing...";
  match parse_from_string preprocessed_code with
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
      let (global_info, ssa_ir) = Ast_to_ssa.convert_program ast in
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
      match Codegen.codegen_program global_info optimized_ssa_ir with
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

  (* Simple test case with a float *)
  let input_code =
    if is_test then
"
int g;
double y;

int
main()
{
    double x;
    g = 5;
    x = 1.5;
    y = x + 2.0;
    if (y > 1.0) {
      return g;
    }
    return 0;
}
      "
    else
      read_all_from_channel stdin
  in
  process_input input_code is_verbose is_test
