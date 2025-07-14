(* file ast.ml *)
(* 操作符类型 *)

(* C 类型系统 *)
type c_type =
  | TVoid
  | TChar
  | TInt
  | TFloat
  | TDouble
  | TStruct of string
  | TUnion of string
  | TEnum of string
  | TPtr of c_type
  | TArray of c_type * int

type binop =
  | Add | Sub | Mul | Div | Mod
  | Le  (* Less than or equal <= *)
  | Eq  (* Equal == *)
  | Ne  (* Not equal != *)
  | Lt  (* Less than < *)
  | Gt  (* Greater than > *)
  | Ge  (* Greater than or equal >= *)
  | BitAnd | BitOr | BitXor

(* 表达式类型 *)
type expr =
  | CstI of int                     (* 整型常量: e.g., 1, 42 *)
  | CstF of float                   (* 浮点型常量: e.g., 3.14 *)
  | CstS of string                  (* 字符串字面量: e.g., "hello" *)
  | Id of string                    (* 标识符/变量: e.g., n *)
  | BinOp of binop * expr * expr    (* 二元运算: e.g., n * fac(n-1) *)
  | Call of string * expr list      (* 函数调用: e.g., fac(4) *)
  | AddrOf of expr                  (* 取址操作: &v *)
  | Deref of expr                   (* 解引用操作: *p *)
  | ArrayAccess of expr * expr      (* 数组元素访问: e.g., arr[index] *)
  | MemberAccess of expr * string   (* 结构体成员访问: s.field *)
  | PtrMemberAccess of expr * string(* 结构体指针成员访问: p->field *)

(* 语句类型 *)
type stmt =
  | Return of expr                  (* return 语句: e.g., return 1; *)
  | DoWhile of stmt * expr          (* do-while 循环: do { body } while (cond); *)
  | While of expr * stmt            (* while 循环: while (cond) { body } *)
  | If of expr * stmt * stmt option (* if (cond) { then } else { else } *)
  | Block of stmt list              (* 代码块: { stmt1; stmt2; ... } *)
  | Decl of c_type * string * expr option (* 变量声明: e.g., int x; int x = 5; *)
  | ArrayDecl of c_type * string * expr (* 数组声明: e.g., int arr[10]; *)
  | Assign of expr * expr           (* 赋值语句: e.g., x = 5; arr[0] = 10; *)
  | ExprStmt of expr                (* 表达式作为语句: e.g., func(); *)

(* 函数定义 *)
type func_def = {
  ret_type : c_type;                    (* 返回类型 *)
  name     : string;                    (* 函数名, e.g., "fac" *)
  params   : (c_type * string) list;    (* 参数列表 (类型, 名称) *)
  body     : stmt;                      (* 函数体, 是一个 Block *)
}

(* 结构体定义 *)
type struct_def = {
  s_name: string;
  s_members: (c_type * string) list;
}

(* 联合体定义 *)
type union_def = {
  u_name: string;
  u_members: (c_type * string) list;
}

(* 枚举定义 *)
type enum_def = {
  e_name: string option;
  e_members: (string * expr option) list;
}

(* 顶层定义 *)
type global_def =
  | GFunc of func_def | GVar of c_type * string * expr option | GArray of c_type * string * expr
  | GStructDef of struct_def | GUnionDef of union_def | GEnumDef of enum_def

(* 一个程序是顶层定义的列表 *)
type program = global_def list


