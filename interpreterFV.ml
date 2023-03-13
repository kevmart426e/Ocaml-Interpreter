(* INTERPRETER *)

let and_then (f : 'a -> ('b, 'e) result) (res : ('a, 'e) result): ('b, 'e) result =
  Result.bind res f

let all_ok (ls : ('a, 'e) result list): ('a list, 'e) result =
  let combine_result a b =
    a |> and_then @@ fun a ->
    b |> and_then @@ fun b ->
    Ok(b :: a)
  in
  List.fold_left combine_result (Ok([])) ls |> Result.map List.rev

(*THE PROGRAM DEFINITIONS*)

type var = Var of string

type const =
  | Int of int
  | String of string
  | Name of var

type com =
  | Quit
  | Push of const
  | Pop
  | Add
  | Sub
  | Mul
  | Div
  | Swap
  | Neg
  | Concat
  | And
  | Or
  | Not
  | Equal
  | Lte
  | Local of var
  | Global of var
  | BeginEnd of prog
  | IfThenElse of prog * prog
  | InjL
  | InjR

and prog = com list

and value =
  | VInt of int
  | VString of string
  | VRight of string
  | VLeft of string

type stack = value list
type log = string list

type env = (var * value) list
type state = stack * log * (* local *) env * (* global *) env

let int_of_bool (b : bool): int =
  if b then 1 else 0

let is_bool (n : int): bool =
  n = 0 || n = 1

let lookup_bind (x : var) (envs : env * env): value option =
  let rec lookup e =
    match e with
    | [] -> None
    | (y, v)::rst -> if y = x
                     then Some(v)
                     else lookup rst
  in
  let (local, global) = envs in
  match lookup local with
  | None -> lookup global
  | Some(v) -> Some(v)

let add_bind (x : var) (v : value) (e : env): env  =
  let updated, e =
      List.fold_left
        (fun (updated, acc) (y, v') ->
          if y = x
          then true, (y, v)::acc
          else updated, (y, v')::acc)
        (false, [])
        e
  in
  let e = List.rev e in
  if updated then e else (x, v)::e

let com_arity (c : com): int =
  match c with
  | Quit | Push(_) | BeginEnd(_) | IfThenElse(_) -> 0
  | Pop  | Neg | Not | Local(_) | Global(_) -> 1
  | Add  | Sub | Mul | Div | Swap | Concat | And | Or | Equal | Lte | InjR |  InjL  -> 2


(*PRINTER FUNCTIONS*)
let string_of_const c =
  match c with
  | Int(i)       -> string_of_int i
  | String(s)    -> "\"" ^ s ^ "\""
  | Name(Var(v)) -> v

let string_of_value v =
  match v with
  | VInt(i)    -> string_of_int i
  | VString(s) -> "\"" ^ s ^ "\""
  | VRight(r) -> "Left" ^ r
  | VLeft(l) -> "Right" ^ l

let rec string_of_com (c : com) : string =
  match c with
  | Quit    -> "Quit"
  | Push(c) -> Printf.sprintf "Push %s" (string_of_const c)
  | Pop     -> "Pop"
  | Add     -> "Add"
  | Sub     -> "Sub"
  | Mul     -> "Mul"
  | Div     -> "Div"
  | Swap    -> "Swap"
  | Neg     -> "Neg"
  | Concat  -> "Concat"
  | And     -> "And"
  | Or      -> "Or"
  | Not     -> "Not"
  | Equal   -> "Equal"
  | Lte     -> "Lte"
  | Local (Var(v))   -> Printf.sprintf "Local %s" v
  | Global(Var(v))   -> Printf.sprintf "Local %s" v
  | BeginEnd(p)      ->
     "Begin\n"
   ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev p)
   ^ "\nEnd\n"
  | IfThenElse(t, e) ->
     "IfThen\n"
   ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev t)
   ^ "\nElse\n"
   ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev e)
   ^ "\nEnd\n"
  | InjL  -> "InjL"
  | InjR  -> " InjR"
 

let rec string_of_list (p : 'a -> string) (ls : 'a list): string =
  match ls with
  | []       -> "[]"
  | fst::rst -> p fst ^ "::" ^ string_of_list p rst

(*TOKENIZING*)
let char_list_of_string (s : string): char list =
  List.init (String.length s) (String.get s)

type token =
  | NEWLINE
  | STRING of string
  | NUMBER of int
  | SYMBOL of string

let string_of_token tok =
  match tok with
  | NEWLINE   -> "\\n"
  | STRING(s) -> "\"" ^ s ^ "\""
  | NUMBER(n) -> string_of_int n
  | SYMBOL(s) -> s

let is_space (c : char): bool =
  c = ' ' || c = '\t'

let is_digit (c : char): bool =
  match c with | '0' .. '9' -> true | _ -> false

let is_alpha (c : char): bool =
  match c with | 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

let int_of_char (c : char): int =
  int_of_string @@ Char.escaped c

type lexer_err =
  | UnclosedString of (* line number *) int
  | InvalidChar    of (* line number *) int * char
  | UnknownChar    of (* line number *) int * char

let string_of_lexer_err e =
  match e with
  | UnclosedString(i) -> Printf.sprintf "Unclosed string at line %i" i
  | InvalidChar(i, c) -> Printf.sprintf "Invalid char '%c' at line %i" c i
  | UnknownChar(i, c) -> Printf.sprintf "Unknown char '%c' at line %i" c i


let tokenize_string line_num (ls : char list): (string * char list, lexer_err) result =
  let rec helper ls acc =
    match ls with
    | [] -> Error(UnclosedString(line_num))
    | ch::rst ->
       if ch = '\"' then
         Ok(acc, rst)
       else if is_alpha ch then
         helper rst (acc ^ Char.escaped ch)
       else
         Error(InvalidChar(line_num, ch))
  in helper ls ""

let tokenize_number line_num (ls : char list): (int * char list, lexer_err) result =
  let rec helper ls acc =
    match ls with
    | [] -> Ok(acc, [])
    | ch::rst ->
       if ch = '\n' || is_space ch then
         Ok(acc, ls)
       else if is_digit ch then
         helper rst @@ acc * 10 + int_of_char ch
       else Error(InvalidChar(line_num, ch))
  in helper ls 0

let tokenize_symbol line_num (ls : char list): (string * char list, lexer_err) result =
  let rec helper ls acc =
    match ls with
    | [] -> Ok(acc, [])
    | ch::rst ->
       if ch = '\n' || is_space ch then
         Ok(acc, ls)
       else if is_alpha ch || ch = '_' || is_digit ch then
         helper rst (acc ^ Char.escaped ch)
       else
         Error(InvalidChar(line_num, ch))
  in helper ls ""

let tokenize_source (src : string): (token list, lexer_err) result =
  let rec helper line_num ls acc =
    match ls with
    | [] -> Ok(List.rev @@ acc)
    | ch::rst ->
       match ch with
       | '\n' -> helper (line_num + 1) rst (NEWLINE :: acc)
       | '\"' -> tokenize_string line_num rst |> and_then @@ fun (s, rst) ->
                 helper line_num rst (STRING(s) :: acc)
       | '-'  -> tokenize_number line_num rst |> and_then @@ fun (n, rst) ->
                 helper line_num rst (NUMBER(-1 * n) :: acc)
       | ch when is_digit ch
              -> tokenize_number line_num (ch::rst) |> and_then @@ fun (n, rst) ->
                 helper line_num rst (NUMBER(n) :: acc)
       | ch when is_alpha ch
              -> tokenize_symbol line_num ls |> and_then @@ fun (s, rst) ->
                 helper line_num rst (SYMBOL(s) :: acc)
       | ch when is_space ch -> helper line_num rst acc
       | ch -> Error(UnknownChar(line_num, ch))
  in helper 1 (char_list_of_string src) []


(*PARSING*)
type parse_err =
  | MissingArguments of (* line number *) int
  | InvalidCom       of (* line number *) int * token
  | ExpectedConst    of (* line number *) int * token
  | ExpectedVar      of (* line number *) int * token
  | InvalidVar       of (* line number *) int * token
  | UnexpectedEOF    of (* line number *) int
  | MissingNewline   of (* line number *) int

let string_of_parse_err e =
  match e with
  | MissingArguments(i) ->
     Printf.sprintf "Missing arguments to command at line %i" i
  | InvalidCom(i, tok) ->
     Printf.sprintf "Invalid command at line %i, got: \"%s\"" i (string_of_token tok)
  | ExpectedConst(i, tok) ->
     Printf.sprintf "Expected constant at line %i, got: \"%s\"" i (string_of_token tok)
  | ExpectedVar(i, tok) ->
     Printf.sprintf "Expected a variable name at line %i, got: \"%s\"" i (string_of_token tok)
  | InvalidVar(i, tok) ->
     Printf.sprintf "Invalid variable name at line %i, got: \"%s\"" i (string_of_token tok)
  | UnexpectedEOF(i) ->
     Printf.sprintf "Ran out of tokens at line %i" i
  | MissingNewline(i) ->
     Printf.sprintf "Missing newline on line %i" i

(* DEPENDS ON: Symbol tokens being valid variables with arbitrary case starting char *)
let make_var line_num (s : string): (var, parse_err) result =
  if String.length s <> 0 then
     match String.get s 0 with
     | 'a' .. 'z' -> Ok(Var(s))
     | _ -> Error(InvalidVar(line_num, SYMBOL(s)))
  else Error(InvalidVar(line_num, SYMBOL(s)))

(* Consume a newline from the token list, if it is required and not present, error. *)
let consume_newline (line_num : int) (required : bool) (ls : token list)
                  : (int * token list, parse_err) result =
  match ls with
  | [] -> Ok(line_num, [])
  | NEWLINE::tl -> Ok((line_num + 1, tl))
  |      hd::tl -> if required then
                     Error(MissingNewline(line_num))
                   else
                     Ok(line_num, hd::tl)

(* See: PA4 parse_sexpr *)
let rec parse_com line_num ls : (com * int * token list, parse_err) result =
  let parse_const line_num tok =
    match tok with
    | NUMBER(n) -> Ok(Int(n))
    | STRING(s) -> Ok(String(s))
    | SYMBOL(s) -> make_var line_num s |> Result.map (fun x -> Name(x))
    | tok       -> Error(ExpectedConst(line_num, tok))
  in
  match ls with
  | SYMBOL("Push")  ::fst::rst ->
     parse_const line_num fst |> and_then @@ fun x ->
     Ok(Push(x), line_num, rst)
  | SYMBOL("Quit")  ::rst -> Ok(Quit, line_num, rst)
  | SYMBOL("Pop")   ::rst -> Ok(Pop, line_num, rst)
  | SYMBOL("Add")   ::rst -> Ok(Add, line_num, rst)
  | SYMBOL("Sub")   ::rst -> Ok(Sub, line_num, rst)
  | SYMBOL("Mul")   ::rst -> Ok(Mul, line_num, rst)
  | SYMBOL("Div")   ::rst -> Ok(Div, line_num, rst)
  | SYMBOL("Swap")  ::rst -> Ok(Swap, line_num, rst)
  | SYMBOL("Neg")   ::rst -> Ok(Neg, line_num, rst)
  | SYMBOL("Concat")::rst -> Ok(Concat, line_num, rst)
  | SYMBOL("And")   ::rst -> Ok(And, line_num, rst)
  | SYMBOL("Or")    ::rst -> Ok(Or, line_num, rst)
  | SYMBOL("Not")   ::rst -> Ok(Not, line_num, rst)
  | SYMBOL("Equal") ::rst -> Ok(Equal, line_num, rst)
  | SYMBOL("Lte")   ::rst -> Ok(Lte, line_num, rst)

  | SYMBOL("Local") ::SYMBOL(s)::rst ->
     make_var line_num s |> Result.map @@ fun x -> Local(x), line_num, rst
  | SYMBOL("Local") ::c::rst -> Error(ExpectedVar(line_num, c))

  | SYMBOL("Global")::SYMBOL(s)::rst ->
     make_var line_num s |> Result.map @@ fun x -> Global(x), line_num, rst
  | SYMBOL("Global")::c::rst -> Error(ExpectedVar(line_num, c))

  | SYMBOL("Begin") ::rst ->
     consume_newline line_num false rst
     |> and_then @@ fun (line_num, rst) ->
     parse_com_list line_num (SYMBOL("End")) rst
     |> and_then @@ fun (blk, line_num, rst) ->
     Ok(BeginEnd(blk), line_num, rst)

  | SYMBOL("IfThen")::rst ->
     consume_newline line_num false rst
       |> and_then @@ fun (line_num, rst) ->
     parse_com_list line_num (SYMBOL("Else")) rst
       |> and_then @@ fun (then_blk, line_num, rst) ->
     consume_newline line_num false rst
       |> and_then @@ fun (line_num, rst) ->
     parse_com_list line_num (SYMBOL("End")) rst
       |> and_then @@ fun (else_blk, line_num, rst) ->
     Ok(IfThenElse(then_blk, else_blk), line_num, rst)

  | tok::_ -> Error(InvalidCom(line_num, tok))
  | [] -> Error(UnexpectedEOF(line_num))


(* See: PA4 parse_sexpr_list *)
and parse_com_list (line_num : int) (terminator : token) (ls : token list)
                 : (prog * int * token list, parse_err) result =
    match ls with
    | fst::rst when fst = terminator -> Ok([], line_num, rst)
    | _  -> parse_com line_num ls
              |> and_then @@ fun (fst, line_num, ls') ->
            consume_newline line_num true ls'
              |> and_then @@ fun (line_num, ls'') ->
            parse_com_list line_num terminator ls''
              |> and_then @@ fun (rst, line_num, ls''') ->
            Ok((fst::rst, line_num, ls'''))

(* See: PA4 parse *)
let parse_program (src : token list): (prog, parse_err) result  =
  let rec parse_all line_num ls acc  =
    match ls with
    | [] -> Ok(List.rev acc)
    | _  -> parse_com line_num ls
              |> and_then @@ fun (c, line_num, ls) ->
            consume_newline line_num true ls
              |>  and_then @@ fun (line_num, ls) ->
            parse_all line_num ls (c::acc)
  in
  parse_all 1 src []

(*EVALUATION*)

type eval_err =
  | InvalidArity of com * (* # got *) int
  | WrongType    of com * (* args got *) value list
  | DivByZero    of int * int
  | UnboundVar   of var
  | NoValue      of com

let string_of_eval_err e =
  match e with
  | InvalidArity(c, i) ->
     Printf.sprintf "Got %i arguments to %s, expected %i" i (string_of_com c) (com_arity c)
  | WrongType(_, ls) ->
     Printf.sprintf "Got arguments of incorrect type: " ^ string_of_list string_of_value ls
  | DivByZero(m, n) ->
     Printf.sprintf "Got arguments to div: %i / %i" m n
  | UnboundVar(Var(s)) ->
     Printf.sprintf "Unbound variable %s" s
  | NoValue(c) ->
     Printf.sprintf "Expected return value from command %s" (string_of_com c)

let with_stack (f : stack -> (stack, 'e) result) (s, l, loc, glob : state): (state, 'e) result =
  f s |> Result.map (fun s -> s, l, loc, glob)

(*PROGRAM METHODS*)
let quit (stk, log, loc, glob : state): state =
  stk
  , (List.fold_right
       (fun elem acc -> string_of_value elem :: acc)
       stk
       [])
    @ log
  , loc
  , glob

let push (stk, log, loc, glob : state) (c : const): (state, eval_err) result =
  match c with
  | Name(v)   -> lookup_bind v (loc, glob)
              |> Option.to_result ~none:(UnboundVar(v))
              |> Result.map (fun x -> x::stk, log, loc, glob)
  | String(s) -> Ok(VString(s) :: stk, log, loc, glob)
  | Int(n)    -> Ok(VInt(n) :: stk, log, loc, glob)

let pop : state -> (state, eval_err) result =
  with_stack @@
    function
    | []    -> Error(InvalidArity(Pop, 0))
    | _::tl -> Ok(tl)

let add : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: VInt(y) :: rst -> Ok(VInt(x + y) :: rst)
    | _ :: [] | [] as stk       -> Error(InvalidArity(Add, List.length stk))
    | x :: y :: _               -> Error(WrongType(Add, [x; y]))

let sub : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: VInt(y) :: rst -> Ok(VInt(x - y) :: rst)
    | _ :: [] | [] as stk       -> Error(InvalidArity(Sub, List.length stk))
    | x :: y :: _               -> Error(WrongType(Sub, [x; y]))

let mul : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: VInt(y) :: rst -> Ok(VInt(x * y) :: rst)
    | _ :: [] | [] as stk       -> Error(InvalidArity(Mul, List.length stk))
    | x :: y :: _               -> Error(WrongType(Mul, [x; y]))

let div : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: VInt(0) :: _   -> Error(DivByZero(x, 0))
    | VInt(x) :: VInt(y) :: rst -> Ok(VInt(x / y) :: rst)
    | _ :: [] | [] as stk       -> Error(InvalidArity(Div, List.length stk))
    | x :: y :: _               -> Error(WrongType(Div, [x; y]))

let swap : state -> (state, eval_err) result =
  with_stack @@
    function
    | x :: y :: rst       -> Ok(y :: x :: rst)
    | _ :: [] | [] as stk -> Error(InvalidArity(Swap, List.length stk))

let neg : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: rst -> Ok(VInt(-1 * x) :: rst)
    | []             -> Error(InvalidArity(Neg, 0))
    | x :: _         -> Error(WrongType(Neg, [x]))

let concat : state -> (state, eval_err) result =
  with_stack @@
    function
    | VString(x) :: VString(y) :: rst -> Ok(VString(x ^ y) :: rst)
    | _ :: [] | [] as stk             -> Error(InvalidArity(Concat, List.length stk))
    | x :: y :: _                     -> Error(WrongType(Concat, [x; y]))

let and_ : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: VInt(y) :: rst when is_bool x && is_bool y
                          -> Ok(VInt(int_of_bool (x = y)) :: rst)
    | _ :: [] | [] as stk -> Error(InvalidArity(And, List.length stk))
    | x :: y :: _         -> Error(WrongType(And, [x; y]))

let or_ : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: VInt(y) :: rst when is_bool x && is_bool y
                          -> Ok(VInt(int_of_bool (x = 1 || y = 1)) :: rst)
    | _ :: [] | [] as stk -> Error(InvalidArity(Or, List.length stk))
    | x :: y :: _         -> Error(WrongType(Or, [x; y]))

let not_ : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: rst when is_bool x
             -> Ok(VInt(abs(x - 1)) :: rst)
    | []     -> Error(InvalidArity(Not, 0))
    | x :: _ -> Error(WrongType(Not, [x]))

let equal : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: VInt(y) :: rst -> Ok(VInt(int_of_bool (x = y)) :: rst)
    | _ :: [] | [] as stk       -> Error(InvalidArity(Equal, List.length stk))
    | x :: y :: _               -> Error(WrongType(Equal, [x; y]))

let lte : state -> (state, eval_err) result =
  with_stack @@
    function
    | VInt(x) :: VInt(y) :: rst -> Ok(VInt(int_of_bool (x <= y)) :: rst)
    | _ :: [] | [] as stk       -> Error(InvalidArity(Lte, List.length stk))
    | x :: y :: _               -> Error(WrongType(Lte, [x; y]))

let injR : state -> (state, eval_err) result =
  with_stack @@
    function
    | x :: rst -> Ok((VRight(string_of_value x)) :: rst)
    | []    -> Error(InvalidArity(InjR, 0))

let injL : state -> (state, eval_err) result =
  with_stack @@
    function
    | x :: rst -> Ok((VLeft(string_of_value x)) :: rst)
    | []    -> Error(InvalidArity(InjR, 0))    


let local (s, l, loc, glob : state) (x : var) : (state, eval_err) result =
  match s with
  | v::rst -> Ok((rst, l, add_bind x v loc, glob))
  | []     -> Error(InvalidArity(Local(x), 0))
  

let global (s, l, loc, glob : state) (x : var) : (state, eval_err) result =
  match s with
  | v::rst -> Ok((rst, l, loc, add_bind x v glob))
  | []     -> Error(InvalidArity(Global(x), 0))

let rec begin_end (s, l, loc, glob : state) (blk : prog): (bool * state, eval_err) result =
  eval blk ([], l, loc, glob) |> and_then @@ fun (quitting, (s', l, _, glob)) ->
  match s' with
  | v::rst -> Ok((quitting, (v::s, l, loc, glob)))
  | []     -> Error(NoValue(BeginEnd(blk)))

and ifthen_else (s, l, loc, glob : state) (then_blk : prog) (else_blk : prog): (bool * state, eval_err) result =
  match s with
  | VInt(v)::rst when v = 1
    -> eval then_blk (rst, l, loc, glob)
  | VInt(v)::rst when v = 0
    -> eval else_blk (rst, l, loc, glob)
  | []     -> Error(InvalidArity(IfThenElse(then_blk, else_blk), 0))
  | x::rst -> Error(WrongType(IfThenElse(then_blk, else_blk), [x]))



and eval (prog : prog) (st : state) : (bool * state, eval_err) result =
  match prog with
  | []                -> Ok(false, st)
  | Quit      :: _    -> Ok(true, quit st)
  | Push(c)   :: prog -> push   st c |> and_then (eval prog)
  | Pop       :: prog -> pop    st   |> and_then (eval prog)
  | Add       :: prog -> add    st   |> and_then (eval prog)
  | Sub       :: prog -> sub    st   |> and_then (eval prog)
  | Mul       :: prog -> mul    st   |> and_then (eval prog)
  | Div       :: prog -> div    st   |> and_then (eval prog)
  | Swap      :: prog -> swap   st   |> and_then (eval prog)
  | Neg       :: prog -> neg    st   |> and_then (eval prog)
  | And       :: prog -> and_   st   |> and_then (eval prog)
  | Or        :: prog -> or_    st   |> and_then (eval prog)
  | Not       :: prog -> not_   st   |> and_then (eval prog)
  | Lte       :: prog -> lte    st   |> and_then (eval prog)
  | Concat    :: prog -> concat st   |> and_then (eval prog)
  | Equal     :: prog -> equal  st   |> and_then (eval prog)
  | Local(x)  :: prog -> local  st x |> and_then (eval prog)
  | Global(x) :: prog -> global st x |> and_then (eval prog)

  | BeginEnd(p)      :: prog -> begin_end st p
                                |> and_then @@ fun (quitting, st) ->
                                if not quitting then eval prog st else Ok(quitting, st)
  | IfThenElse(t, e) :: prog -> ifthen_else st t e
                                |> and_then @@ fun (quitting, st) ->
                                if not quitting then eval prog st else Ok(quitting, st)
  | InjR    :: prog -> injR st   |> and_then (eval prog)
  | InjL    :: prog -> injL st   |> and_then (eval prog)

let write_file_with_log (file_path: string) (log: log) : unit =
  let fp = open_out file_path in
    let _ =
      List.fold_left (
        fun items_left elem ->
          match items_left with
          | 1 -> Printf.fprintf fp "%s" elem; items_left - 1
          | _ -> Printf.fprintf fp "%s\n" elem; items_left - 1
      ) (List.length log) log
    in close_out fp

type interp_err =
  | LexerErr of lexer_err
  | ParseErr of parse_err
  | EvalErr  of eval_err

let lexer_err e = LexerErr(e)
let parse_err e = ParseErr(e)
let eval_err  e = EvalErr(e)

let string_of_interp_err e =
  match e with
  | LexerErr(e) -> string_of_lexer_err e
  | ParseErr(e) -> string_of_parse_err e
  | EvalErr(e)  -> string_of_eval_err  e

let interpreter (src : string) (output_file_path: string): unit =
  let run src =
    tokenize_source src        |> Result.map_error lexer_err |> and_then @@ fun tokens ->
    parse_program tokens       |> Result.map_error parse_err |> and_then @@ fun prog ->
    eval prog ([], [], [], []) |> Result.map_error eval_err
  in
  (match run src with
   | Ok(_, (_, log, _, _)) -> log
   | Error(e)      -> print_endline (string_of_interp_err e); ["\"Error\""])
  |> write_file_with_log output_file_path
