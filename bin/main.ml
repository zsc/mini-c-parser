(* file: bin/main.ml *)

(* I. AST Definition *)

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
  | ArrayDecl of string * string * expr (* 数组声明: e.g., int arr[10]; (size expr is required for local arrays) *)
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

type token =
  (* Keywords *)
  | T_Int | T_Return | T_If | T_Else
  (* Identifiers and Literals *)
  | T_Id of string
  | T_Num of int
  (* Operators *)
  | T_Plus | T_Minus | T_Star | T_Slash
  | T_Le | T_Eq | T_Ne | T_Lt | T_Gt | T_Ge
  (* Delimiters *)
  | T_Lparen | T_Rparen (* ( ) *)
  | T_Assign (* = *)
  | T_Lbrace | T_Rbrace (* { } *)
  | T_Lbracket | T_Rbracket (* [ ] *)
  | T_Comma
  | T_Semicolon
  (* End of File *)
  | T_Eof

let keyword_map = [
  ("int", T_Int);
  ("return", T_Return);
  ("if", T_If);
  ("else", T_Else);
]

let token_specs = [
  (* Whitespace (ignored) *)
  (Str.regexp "[ \t\n\r]+", fun _ -> None);
  (* Comments (ignored) *)
  (Str.regexp "//[^\n]*", fun _ -> None);
  (Str.regexp "/\\*.*?\\*/", fun _ -> None);

  (* Keywords and Identifiers *)
  (Str.regexp "[a-zA-Z_][a-zA-Z0-9_]*", fun s ->
    try Some (List.assoc s keyword_map)
    with Not_found -> Some (T_Id s));

  (* Numeric Literals *)
  (Str.regexp "[0-9]+", fun s -> Some (T_Num (int_of_string s)));

  (* Operators *)
  (Str.regexp "<=", fun _ -> Some T_Le);
  (Str.regexp "==", fun _ -> Some T_Eq);
  (Str.regexp "!=", fun _ -> Some T_Ne);
  (Str.regexp ">=", fun _ -> Some T_Ge);
  (Str.regexp "<", fun _ -> Some T_Lt);
  (Str.regexp ">", fun _ -> Some T_Gt);
  (Str.regexp "+", fun _ -> Some T_Plus);
  (Str.regexp "-", fun _ -> Some T_Minus);
  (Str.regexp "=", fun _ -> Some T_Assign); (* Must be after ==, <=, >= *)
  (Str.regexp "*", fun _ -> Some T_Star);
  (Str.regexp "/", fun _ -> Some T_Slash);

  (* Delimiters *)
  (Str.regexp "(", fun _ -> Some T_Lparen);
  (Str.regexp ")", fun _ -> Some T_Rparen);
  (Str.regexp "{", fun _ -> Some T_Lbrace);
  (Str.regexp "}", fun _ -> Some T_Rbrace);
  (Str.regexp "\\[", fun _ -> Some T_Lbracket);
  (Str.regexp "\\]", fun _ -> Some T_Rbracket);
  (Str.regexp ",", fun _ -> Some T_Comma);
  (Str.regexp ";", fun _ -> Some T_Semicolon);
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
              | None -> next_token new_pos (* Ignored token *)
            else
              find_match rest_specs
      in
      find_match token_specs
  in
  next_token 0

(* III. Parser *)

(* 一些辅助函数 *)
let expect token tokens =
  match tokens with
  | t :: rest when t = token -> rest
  | t :: _ ->
      failwith (Printf.sprintf "Parser error: Expected %s but found %s"
        (match token with
         | T_Lparen -> "'('" | T_Rparen -> "')'" | T_Lbracket -> "'['"
         | T_Rbracket -> "']'" | T_Lbrace -> "'{'" | T_Assign -> "'='"
         | T_Rbrace -> "'}'" | T_Comma -> "','" | T_Int -> "'int'"
         | T_Semicolon -> "';'"
         | _ -> "token")
        (match t with
         | T_Id s -> "identifier " ^ s | T_Num n -> "number " ^ string_of_int n
         | T_Int -> "'int'" | T_Return -> "'return'" | T_If -> "'if'"
         | _ -> "a token"))
  | [] -> failwith "Parser error: Unexpected end of input"

(* 主解析函数 *)
let rec parse_program tokens : program * token list =
  match tokens with
  | T_Eof :: _ -> ([], tokens) (* If T_Eof is found, no more definitions to parse. Return remaining tokens (which should just be T_Eof). *)
  | _ ->
      let (def, rest_tokens) = parse_top_level_def tokens in
      let (defs, final_tokens) = parse_program rest_tokens in
      (def :: defs, final_tokens)

and parse_top_level_def tokens =
  let rest1 = expect T_Int tokens in
  let name, rest2 = match rest1 with
    | T_Id s :: rest -> s, rest
    | _ -> failwith "Expected function name" in
  let rest3 = expect T_Lparen rest2 in
  let params, rest4 = parse_params rest3 in
  let rest5 = expect T_Rparen rest4 in
  let body, rest6 = parse_stmt rest5 in (* Function body must be a block *)
  ({ ret_type = "int"; name; params; body }, rest6)

and parse_type_name tokens =
  match tokens with
  | T_Int :: T_Lbracket :: T_Rbracket :: rest -> ("int[]", rest)
  | T_Int :: rest -> ("int", rest)
  | _ -> failwith "Expected type name (e.g., 'int' or 'int[]')"

and parse_params tokens =
  match tokens with
  | T_Rparen :: _ -> ([], tokens) (* No parameters *)
  | _ ->
      let rec loop acc tokens =
        let (param_type, rest1) = parse_type_name tokens in
        let name, rest2 = match rest1 with
          | T_Id s :: rest -> s, rest
          | _ -> failwith "Expected parameter name" in
        let new_acc = acc @ [(param_type, name)] in
        match rest2 with
        | T_Comma :: rest' -> loop new_acc rest'
        | _ -> (new_acc, rest2)
      in
      loop [] tokens

and parse_stmt tokens =
  match tokens with
  | T_Return :: rest ->
      let (expr, rest') = parse_expr rest in
      let rest'' = expect T_Semicolon rest' in
      (Return expr, rest'')
  | T_If :: rest ->
      let rest1 = expect T_Lparen rest in
      let (cond, rest2) = parse_expr rest1 in
      let rest3 = expect T_Rparen rest2 in
      let (then_stmt, rest4) = parse_stmt rest3 in
      let (else_stmt, rest_final) =
        match rest4 with
        | T_Else :: rest' ->
            let (stmt, rest'') = parse_stmt rest' in
            (Some stmt, rest'')
        | _ -> (None, rest4)
      in
      (If (cond, then_stmt, else_stmt), rest_final)
  | T_Lbrace :: rest ->
      let rec parse_stmts acc t =
        match t with
        | T_Rbrace :: rest' -> (Block (List.rev acc), rest')
        | _ ->
            let (stmt, t') = parse_stmt t in
            parse_stmts (stmt :: acc) t'
      in
      parse_stmts [] rest (* Start parsing statements within the block *)
  (* New statement types: Decl, ArrayDecl, Assign, ExprStmt *)
  | T_Int :: _ -> (* Potential variable or array declaration *)
      let (decl_type, rest_type) = parse_type_name tokens in (* consumes T_Int, potentially T_Lbracket T_Rbracket *)
      let name, rest_name = match rest_type with
        | T_Id s :: rest -> s, rest
        | _ -> failwith "Expected identifier after type in declaration" in
      (match rest_name with
       | T_Lbracket :: rest_idx -> (* Array declaration: int arr[size]; *)
           let (size_expr, rest_idx') = parse_expr rest_idx in
           let rest_idx'' = expect T_Rbracket rest_idx' in
           let rest_final = expect T_Semicolon rest_idx'' in
           (ArrayDecl (decl_type, name, size_expr), rest_final)
       | T_Assign :: rest_assign -> (* Scalar declaration with initialization: int x = 5; *)
           let (initial_expr, rest_expr) = parse_expr rest_assign in
           let rest_final = expect T_Semicolon rest_expr in
           (Decl (decl_type, name, Some initial_expr), rest_final)
       | T_Semicolon :: rest_final -> (* Scalar declaration without initialization: int x; *)
           (Decl (decl_type, name, None), rest_final)
       | _ -> failwith "Expected '=', '[', or ';' after identifier in declaration"
      )
  | (T_Id _) :: _ as start_tokens -> (* Assignment or function call as statement *)
      (* Try to parse the expression which could be an L-value or a Call *)
      let (first_expr, rest_after_expr) = parse_expr start_tokens in
      (match rest_after_expr with
       | T_Assign :: rest_assign ->
           let (rhs_expr, rest_rhs) = parse_expr rest_assign in
           let rest_final = expect T_Semicolon rest_rhs in
           (Assign (first_expr, rhs_expr), rest_final)
       | T_Semicolon :: rest_final ->
           (* Only function calls, identifiers, or array accesses can be standalone expression statements. *)
           (match first_expr with
            | Call _ | Id _ | ArrayAccess _ -> (ExprStmt first_expr, rest_final)
            | _ -> failwith "Parser error: Only function calls, identifiers, or array accesses can be standalone expression statements." )
       | _ -> failwith "Parser error: Expected '=' or ';' after expression" )
  | _ -> failwith "Parser error: Unexpected token in statement"

(* 表达式解析 (带操作符优先级) *)
and parse_expr tokens = parse_equality_expr tokens

and parse_equality_expr tokens = (* ==, != *)
  let rec loop lhs toks =
    match toks with
    | T_Eq :: rest ->
        let (rhs, rest') = parse_relational_expr rest in
        loop (BinOp (Eq, lhs, rhs)) rest'
    | T_Ne :: rest ->
        let (rhs, rest') = parse_relational_expr rest in
        loop (BinOp (Ne, lhs, rhs)) rest'
    | _ -> (lhs, toks)
  in
  let (lhs, rest) = parse_relational_expr tokens in
  loop lhs rest
 
and parse_relational_expr tokens = (* <, <=, >, >= *)
  let rec loop lhs toks =
    match toks with
    | T_Lt :: rest ->
        let (rhs, rest') = parse_additive_expr rest in
        loop (BinOp (Lt, lhs, rhs)) rest'
    | T_Le :: rest ->
        let (rhs, rest') = parse_additive_expr rest in
        loop (BinOp (Le, lhs, rhs)) rest'
    | T_Gt :: rest ->
        let (rhs, rest') = parse_additive_expr rest in
        loop (BinOp (Gt, lhs, rhs)) rest'
    | T_Ge :: rest ->
        let (rhs, rest') = parse_additive_expr rest in
        loop (BinOp (Ge, lhs, rhs)) rest'
    | _ -> (lhs, toks)
  in
  let (lhs, rest) = parse_additive_expr tokens in
  loop lhs rest
 
and parse_additive_expr tokens = (* +, - *)
  let rec loop lhs toks =
    match toks with
    | T_Plus :: rest ->
        let (rhs, rest') = parse_multiplicative_expr rest in
        loop (BinOp (Add, lhs, rhs)) rest'
    | T_Minus :: rest ->
        let (rhs, rest') = parse_multiplicative_expr rest in
        loop (BinOp (Sub, lhs, rhs)) rest'
    | _ -> (lhs, toks)
  in
  let (lhs, rest) = parse_multiplicative_expr tokens in
  loop lhs rest
 
and parse_multiplicative_expr tokens = (* *, / *)
  let rec loop lhs toks =
    match toks with
    | T_Star :: rest ->
        let (rhs, rest') = parse_unary_expr rest in (* Changed to parse_unary_expr *)
        loop (BinOp (Mul, lhs, rhs)) rest'
    | T_Slash :: rest ->
        let (rhs, rest') = parse_unary_expr rest in (* Changed to parse_unary_expr *)
        loop (BinOp (Div, lhs, rhs)) rest'
    | _ -> (lhs, toks)
  in
  let (lhs, rest) = parse_unary_expr tokens in (* Changed to parse_unary_expr *)
  loop lhs rest
 
(* New: Unary expressions (e.g., -x, +x) *)
and parse_unary_expr tokens =
  match tokens with
  | T_Minus :: rest ->
      let (expr, rest') = parse_unary_expr rest in (* Allows chaining like --x *)
      (BinOp (Sub, Cst 0, expr), rest') (* Represent -expr as (0 - expr) *)
  | T_Plus :: rest -> (* Unary plus, typically a no-op, just consume *)
      parse_unary_expr rest
  | _ ->
      parse_primary_expr tokens
 

and parse_primary_expr tokens =
  match tokens with
  | T_Num n :: rest -> (Cst n, rest)
  | T_Id s :: rest ->
      (* This 's' could be a function name or an array name or a variable name *)
      (* parse_postfix_expr will consume (args) or [index] if present *)
      parse_postfix_expr (Id s) rest
  | T_Lparen :: rest ->
      let (expr, rest') = parse_expr rest in
      let rest'' = expect T_Rparen rest' in
      parse_postfix_expr expr rest'' (* The expression inside parentheses can also be a base for postfix operations *)
  | _ -> failwith "Parser error: Unexpected token in expression"

(* This function takes a 'base' expression (e.g., an Id) and applies
   postfix operations like function calls or array accesses. *)
and parse_postfix_expr current_expr tokens =
  match tokens with
  | T_Lparen :: _ -> (* This is a function call *)
      let func_name = match current_expr with
        | Id s -> s
        | _ -> failwith "Parser error: Function name must be an identifier"
      in
      let rest1 = expect T_Lparen tokens in
      let (args, rest2) = parse_args rest1 in (* Helper to parse argument list *)
      let rest3 = expect T_Rparen rest2 in
      let call_expr = Call (func_name, args) in
      parse_postfix_expr call_expr rest3 (* Allows f()() or f()[0] *)
  | T_Lbracket :: rest -> (* This is an array access *)
      let (index_expr, rest') = parse_expr rest in
      let rest'' = expect T_Rbracket rest' in
      let array_access_expr = ArrayAccess (current_expr, index_expr) in
      parse_postfix_expr array_access_expr rest'' (* Allows arr[i][j] *)
  | _ -> (current_expr, tokens) (* No more postfix operations *)

(* Helper for parsing argument list of a function call *)
and parse_args tokens =
  match tokens with
  | T_Rparen :: _ -> ([], tokens) (* No arguments, Rparen is next *)
  | _ -> let rec loop acc toks = let (arg, toks') = parse_expr toks in let new_acc = acc @ [arg] in match toks' with | T_Comma :: rest -> loop new_acc rest | _ -> (new_acc, toks') in loop [] tokens

(* IV. AST Pretty Printer (for testing) *)

let rec string_of_expr = function
  | Cst n -> string_of_int n
  | Id s -> s
  | BinOp (op, e1, e2) ->
      let op_str = match op with
        | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"
        | Le -> "<=" | Eq -> "==" | Ne -> "!=" | Lt -> "<"
        | Gt -> ">" | Ge -> ">="
      in
      Printf.sprintf "(%s %s %s)" (string_of_expr e1) op_str (string_of_expr e2)
  | Call (name, args) ->
      let args_str = String.concat ", " (List.map string_of_expr args) in
      Printf.sprintf "%s(%s)" name args_str
  | ArrayAccess (base, index) ->
      Printf.sprintf "%s[%s]" (string_of_expr base) (string_of_expr index)
      
let rec string_of_stmt indent = function
  | Return e -> indent ^ "Return " ^ (string_of_expr e)
  | If (cond, then_s, else_s_opt) ->
      let else_str = match else_s_opt with
        | None -> ""
        | Some s -> "\n" ^ indent ^ "Else\n" ^ (string_of_stmt (indent ^ "  ") s)
      in
      indent ^ "If (" ^ (string_of_expr cond) ^ ")\n" ^
      (string_of_stmt (indent ^ "  ") then_s) ^ else_str
  | Block stmts ->
      indent ^ "{\n" ^
      (String.concat "\n" (List.map (string_of_stmt (indent ^ "  ")) stmts)) ^
      "\n" ^ indent ^ "}"
  | Decl (typ, name, init_opt) ->
      let init_str = match init_opt with
        | Some e -> Printf.sprintf " = %s" (string_of_expr e)
        | None -> ""
      in
      Printf.sprintf "%sDecl %s %s%s;" indent typ name init_str
  | ArrayDecl (typ, name, size_expr) ->
      Printf.sprintf "%sArrayDecl %s %s[%s];" indent typ name (string_of_expr size_expr)
  | Assign (lhs, rhs) ->
      Printf.sprintf "%sAssign %s = %s;" indent (string_of_expr lhs) (string_of_expr rhs)
  | ExprStmt e ->
      Printf.sprintf "%sExprStmt %s;" indent (string_of_expr e)


let string_of_def (d : top_level_def) =
  let params_str = String.concat ", " (List.map (fun (t, n) -> t ^ " " ^ n) d.params) in
  Printf.sprintf "Function %s %s(%s)\n%s" d.ret_type d.name params_str (string_of_stmt "" d.body)

let string_of_program (p : program) =
  String.concat "\n\n" (List.map string_of_def p)

(* V. Main Function: string -> AST *)
let parse_from_string str : (program, string) result =
  try
    let tokens = tokenize str in
    let (ast, rest_tokens) = parse_program tokens in
    match rest_tokens with
    | [T_Eof] -> Ok ast
    | _ -> Error "Parser error: Did not consume all tokens"
  with
  | Failure msg -> Error msg


(* VI. Test in Main *)
let () =
  let input_code = "
    int get_element(int[] arr, int index) {
      if (index < 0) {
        return -1; // Error for negative index
      }
      return arr[index];
    }

    int main() {
      int my_var = 10; // Scalar declaration with initialization
      int my_array[3]; // Array declaration
      int x; // Scalar declaration

      my_array[0] = 100; // Array element assignment
      my_array[1] = 200;
      my_array[2] = 300;

      x = my_array[0] + my_array[1]; // Assignment with array access
      x = x + get_element(my_array, 2); // Function call with array parameter

      return x;
    }
  " in

  print_endline "--- Mini-C Parser Test ---";
  print_endline "Input Code:";
  print_endline input_code;
  print_endline "--------------------------";

  match parse_from_string input_code with
  | Ok ast ->
      print_endline "Successfully parsed. Generated AST:";
      print_endline (string_of_program ast)
  | Error msg ->
      print_endline ("Parsing failed: " ^ msg)
