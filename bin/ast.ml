(* ast.ml *)
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
  | AddrOf of expr                  (* 取址操作: &v *)
  | Deref of expr                   (* 解引用操作: *p *)
  | ArrayAccess of expr * expr      (* 数组元素访问: e.g., arr[index] *)

(* 语句类型 *)
type stmt =
  | Return of expr                  (* return 语句: e.g., return 1; *)
  | While of expr * stmt            (* while 循环: while (cond) { body } *)
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


