(* file: bin/main.ml *)

(*
  OCaml Mini-C Compiler to LLVM IR
  =================================

  To compile and run:
  1. Install LLVM bindings: `opam install llvm`
  2. Compile: `ocamlfind ocamlopt -package llvm -linkpkg -o compiler main.ml`
     (or `ocamlbuild -use-ocamlfind -pkg llvm compiler.native`)
  3. Run: `./compiler`

  The program will parse the hardcoded C source, print the AST,
  and then print the generated LLVM IR.
*)


(* I. AST Definition *)
(* (与你提供的代码相同) *)

(* 操作符类型 *)
type binop =
  | Add | Sub | Mul | Div
  | Le  (* Less than or equal <= *)
  | Eq  (* Equal == *)
  | Ne  (* Not equal != *)
  | Lt  (* Less than < *)
  | Gt  (* Greater than > *)
  | Ge  (* Greater than or equal >= *)

(* 表达式类型 *)
type expr =
  | Cst of int                      (* 常量: e.g., 1, 42 *)
  | Id of string                    (* 标识符/变量: e.g., n *)
  | BinOp of binop * expr * expr    (* 二元运算: e.g., n * fac(n-1) *)
  | Call of string * expr list      (* 函数调用: e.g., fac(4) *)
  | ArrayAccess of expr * expr      (* 数组元素访问: e.g., arr[index] *)

(* 语句类型 *)
type stmt =
  | Return of expr                  (* return 语句: e.g., return 1; *)
  | If of expr * stmt * stmt option (* if (cond) { then } else { else } *)
  | Block of stmt list              (* 代码块: { stmt1; stmt2; ... } *)
  | Decl of string * string * expr option (* 变量声明: e.g., int x; int x = 5; *)
  | ArrayDecl of string * string * expr (* 数组声明: e.g., int arr[10]; *)
  | Assign of expr * expr           (* 赋值语句: e.g., x = 5; arr[0] = 10; *)
  | ExprStmt of expr                (* 表达式作为语句: e.g., func(); *)

(* 顶层定义 (目前只有函数) *)
type top_level_def = {
  ret_type : string;                    (* 返回类型, e.g., "int" *)
  name     : string;                    (* 函数名, e.g., "fac" *)
  params   : (string * string) list;    (* 参数列表 (类型, 名称), e.g., [("int", "n")] *)
  body     : stmt;                      (* 函数体, 是一个 Block *)
}

(* 一个程序是顶层定义的列表 *)
type program = top_level_def list


(* II. Tokenizer (Lexer) *)
(* (与你提供的代码相同) *)

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
(* (与你提供的代码大部分相同, 修复了一个小 bug 并且让它更健壮) *)

exception Parser_error of string

let fail_parse msg = raise (Parser_error msg)

let expect token tokens =
  match tokens with
  | t :: rest when t = token -> rest
  | t :: _ -> fail_parse (Printf.sprintf "Expected a certain token but found another")
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
    | _, t :: _ -> Error "Parser error: Did not consume all tokens."
    | _ -> Error "Parser error: Unknown."
  with
  | Parser_error msg -> Error ("Parser error: " ^ msg)
  | Failure msg -> Error ("Lexer/Parser failure: " ^ msg)

(* IV. Code Generation (to LLVM IR) *)

module Codegen = struct
  let the_context = Llvm.global_context ()
  let the_module = Llvm.create_module the_context "mini-c-compiler"
  let builder = Llvm.builder the_context
  let i32_type = Llvm.i32_type the_context
  let void_type = Llvm.void_type the_context

  (* 符号表: 存储变量名到其在栈上的地址 (llvalue) *)
  (* A new symbol table is created for each function. *)
  let named_values : (string, Llvm.llvalue) Hashtbl.t = Hashtbl.create 10

  (* Helper to get a function's LLVM type *)
  let get_llvm_type = function
    | "int" -> i32_type
    | "void" -> void_type (* For future use *)
    | _ -> failwith "Unsupported type"

  (* Look up a function in the module, error if not found. *)
  let get_function name =
    match Llvm.lookup_function name the_module with
    | Some f -> f
    | None -> failwith ("Codegen error: Unknown function referenced: " ^ name)

  let rec codegen_expr expr =
    match expr with
    | Cst i -> Llvm.const_int i32_type i
    | Id s ->
        let ptr = try Hashtbl.find named_values s
                  with Not_found -> failwith ("Codegen error: Unknown variable name: " ^ s) in
        (* Load the value from the stack pointer *)
        Llvm.build_load i32_type ptr s builder
    | BinOp (op, e1, e2) ->
        let v1 = codegen_expr e1 in
        let v2 = codegen_expr e2 in
        (match op with
        | Add -> Llvm.build_add v1 v2 "addtmp" builder
        | Sub -> Llvm.build_sub v1 v2 "subtmp" builder
        | Mul -> Llvm.build_mul v1 v2 "multmp" builder
        | Div -> Llvm.build_sdiv v1 v2 "divtmp" builder
        | Lt -> Llvm.build_icmp Llvm.Icmp.Slt v1 v2 "cmptmp" builder
        | Le -> Llvm.build_icmp Llvm.Icmp.Sle v1 v2 "cmptmp" builder
        | Gt -> Llvm.build_icmp Llvm.Icmp.Sgt v1 v2 "cmptmp" builder
        | Ge -> Llvm.build_icmp Llvm.Icmp.Sge v1 v2 "cmptmp" builder
        | Eq -> Llvm.build_icmp Llvm.Icmp.Eq v1 v2 "cmptmp" builder
        | Ne -> Llvm.build_icmp Llvm.Icmp.Ne v1 v2 "cmptmp" builder
        )
    | Call (name, args) ->
        let callee = get_function name in
        let arg_vals = Array.of_list (List.map codegen_expr args) in
        (* The original code `Llvm.build_call callee ...` is correct for standard LLVM bindings
         * (where the first argument is the function's Llvm.llvalue).
         * If `dune build` reports `callee` has type `Llvm.llvalue` but `Llvm.lltype` was expected,
         * it implies a highly unusual or very old LLVM binding version is in use. *)
        Llvm.build_call (Llvm.type_of callee) callee arg_vals "calltmp" builder
    | ArrayAccess (_, _) -> failwith "Array access codegen not yet implemented"

  let rec codegen_stmt stmt =
    match stmt with
    | Block stmts -> List.iter codegen_stmt stmts
    | ExprStmt e -> ignore (codegen_expr e)
    | Return e -> ignore (Llvm.build_ret (codegen_expr e) builder)
    | If (cond, then_s, else_s_opt) ->
        let cond_val = codegen_expr cond in
        (* C booleans are 0 (false) or non-zero (true). LLVM needs i1. *)
        let zero = Llvm.const_int i32_type 0 in
        let bool_val = Llvm.build_icmp Llvm.Icmp.Ne cond_val zero "ifcond" builder in

        (* Get the current function to append blocks to. *)
        let start_bb = Llvm.insertion_block builder in
        let the_function = Llvm.block_parent start_bb in

        let then_bb = Llvm.append_block the_context "then" the_function in
        let else_bb = Llvm.append_block the_context "else" the_function in
        let merge_bb = Llvm.append_block the_context "ifcont" the_function in

        (* Create the conditional branch. *)
        ignore (Llvm.build_cond_br bool_val then_bb else_bb builder);

        (* Emit 'then' block. *)
        Llvm.position_at_end then_bb builder;
        codegen_stmt then_s;
        if Llvm.block_terminator (Llvm.insertion_block builder) = None then
            ignore (Llvm.build_br merge_bb builder);

        (* Emit 'else' block. *)
        Llvm.position_at_end else_bb builder;
        (match else_s_opt with
        | Some s -> codegen_stmt s
        | None -> ());
        if Llvm.block_terminator (Llvm.insertion_block builder) = None then
            ignore (Llvm.build_br merge_bb builder);

        (* Reposition builder to the merge block. *)
        Llvm.position_at_end merge_bb builder

    | Decl (_, name, init_opt) ->
        (* Create an alloca for the local variable in the function's entry block. *)
        let func = Llvm.block_parent (Llvm.insertion_block builder) in
        let entry_builder = Llvm.builder_at_entry (Llvm.entry_block func) in
        let alloca = Llvm.build_alloca i32_type name entry_builder in
        Hashtbl.add named_values name alloca;

        (* If there's an initializer, store its value. *)
        (match init_opt with
        | Some e ->
            let init_val = codegen_expr e in
            ignore (Llvm.build_store init_val alloca builder)
        | None -> ())
    | ArrayDecl _ -> failwith "Array declaration codegen not yet implemented"
    | Assign (lhs, rhs) ->
        let value_to_store = codegen_expr rhs in
        let ptr = match lhs with
          | Id s ->
              (try Hashtbl.find named_values s
               with Not_found -> failwith ("Undeclared variable for assignment: " ^ s))
          | _ -> failwith "LHS of assignment must be a variable"
        in
        ignore (Llvm.build_store value_to_store ptr builder)

  let codegen_func_def (fdef: top_level_def) =
    Hashtbl.clear named_values; (* Clear symbol table for new function *)

    let the_function = get_function fdef.name in
    let bb = Llvm.append_block the_context "entry" the_function in
    Llvm.position_at_end bb builder;

    (* Allocate space for all parameters and store their initial values *)
    Array.iteri (fun i param_ll ->
      let (param_type, param_name) = List.nth fdef.params i in
      Llvm.set_value_name param_name param_ll;
      let alloca = Llvm.build_alloca (get_llvm_type param_type) param_name builder in
      ignore (Llvm.build_store param_ll alloca builder);
      Hashtbl.add named_values param_name alloca
    ) (Llvm.params the_function);

    codegen_stmt fdef.body;

    (* Verify function and return it *)
    Llvm_analysis.assert_valid_function the_function;
    the_function

  let codegen_program (prog: program) =
    (* Pass 1: Declare all functions so they can be called before being defined (recursion) *)
    List.iter (fun (fdef: top_level_def) ->
      let ret_type = get_llvm_type fdef.ret_type in
      let param_types = Array.of_list (List.map (fun (t,_) -> get_llvm_type t) fdef.params) in
      let f_type = Llvm.function_type ret_type param_types in
      ignore (Llvm.declare_function fdef.name f_type the_module)
    ) prog;

    (* Pass 2: Define all functions *)
    List.iter codegen_func_def prog;

    the_module
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
  | Assign(l, r) -> Printf.sprintf "(%s = %s)" (string_of_expr l) (string_of_expr r)

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
      return fac(4);
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
      let llmodule = Codegen.codegen_program ast in

      (* --- Phase 3: Output --- *)
      print_endline "Successfully generated LLVM IR:";
      print_endline (Llvm.string_of_llmodule llmodule);

      (* Optional: Verify the module for correctness *)
      (match Llvm_analysis.verify_module llmodule with
       | None -> print_endline "\nLLVM module is valid."
       | Some err -> print_endline ("\nLLVM module verification failed:\n" ^ err));

      (* Optional: Write to a file *)
      let output_filename = "output.ll" in
      Llvm.print_module output_filename llmodule;
      Printf.printf "\nLLVM IR also written to %s\n" output_filename
