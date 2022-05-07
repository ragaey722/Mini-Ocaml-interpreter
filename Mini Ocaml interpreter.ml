
type ty = Bool | Int | Arrow of ty * ty
type con = Bcon of bool | Icon of int
type op = Add | Sub | Mul | Leq
type var = string
type exp = Var of var | Con of con
         | Oapp of op * exp * exp
         | Fapp of exp * exp
         | If of exp * exp *exp
         | Lam of var * exp
         | Lamty of var * ty * exp
         | Let of var * exp * exp
         | Letrec of var * var * exp * exp
         | Letrecty of var * var * ty * ty * exp * exp 
                       
type ('a,'b) env = ('a * 'b) list
let empty : ('a,'b) env = []
let update (env : ('a,'b) env) a b : ('a,'b) env = (a,b) :: env
let rec lookup (env : ('a,'b) env) a = match env with
  | (a',b) :: env -> if a = a' then Some b else lookup env a
  | [] -> None         

let check_op o e1 e2 = 
  match o,e1,e2 with 
  |Add,Int,Int -> Int
  |Sub,Int,Int -> Int
  |Mul,Int,Int -> Int
  |Leq,Int,Int -> Bool 
  |_-> failwith "operator: ill-typed arguments"
         
let check_fun t1 t2 = 
  match t1 with 
  |Arrow(input,res)->
      if input = t2 then res
      else failwith "function: wrong argument type" 
  |_-> failwith "function: function type expected"    


let rec check env e : ty = match e with
  | Var x -> 
      begin match lookup env x with 
        | Some t -> t 
        | None-> failwith ("undeclared variable " ^ x) 
      end
  | Con (Bcon b) -> Bool
  | Con (Icon n) -> Int
  | Oapp (o,e1,e2) -> check_op o (check env e1) (check env e2)
  | Fapp (e1,e2) -> check_fun (check env e1) (check env e2)
  | If (e1,e2,e3) ->
      begin match check env e1 with 
        |Bool-> if check env e2 = check env e3 
            then check env e2 
            else failwith "if: unmatched result types"
        |_-> failwith "if:Type bool expected" 
      end
  | Lam (_,_) -> failwith "fun: missing type"
  | Lamty (x,t,e) -> Arrow (t, check (update env x t) e)
  | Let (x,e1,e2) -> check (update env x (check env e1)) e2
  | Letrec (f,x,e1,e2) -> failwith "let rec: missing types"
  | Letrecty (f,x,t1,t2,e1,e2) -> 
      if check (update (update env f (Arrow(t1,t2))) x t1) e1= t2 
      then check (update env f (Arrow(t1,t2)) ) e2 
      else failwith "let rec: unmatched types" 
          

type value = Bval of bool | Ival of int
           | Closure of var * exp * (var, value) env
           | Rclosure of var * var * exp * (var, value) env

let eval_op o v1 v2 = 
  match o, v1, v2 with
  | Add, Ival n1, Ival n2 -> Ival (n1 + n2)
  | Sub, Ival n1, Ival n2 -> Ival (n1 - n2)
  | Mul, Ival n1, Ival n2 -> Ival (n1 * n2)
  | Leq, Ival n1, Ival n2 -> Bval (n1 <= n2)
  | _, _ , _ -> failwith "Operator: ill-typed arguments"
                  

  
let rec eval env e : value = match e with
  | Var x -> 
      begin match lookup env x with 
        |Some v -> v 
        |None -> failwith ("undeclared variable "^x)
      end
  | Con (Bcon b) -> Bval b
  | Con (Icon n) -> Ival n
  | Oapp (o,e1,e2) -> eval_op o (eval env e1) (eval env e2)
  | Fapp (e1,e2) -> eval_fun (eval env e1) (eval env e2)
  | If (e1,e2,e3) -> 
      begin match eval env e1 with
        |Bval b -> 
            begin match b with
              |true-> eval env e2
              |false-> eval env e3 
            end
        |_->failwith "if: Boolean value expected"
      end
  | Lam (x,e) | Lamty (x,_,e) -> Closure (x,e,env)
  | Let (x,e1,e2) -> eval (update env x (eval env e1)) e2
  | Letrec (f,x,e1,e2) | Letrecty (f,x,_,_,e1,e2) -> 
      eval (update env f (Rclosure(f,x,e1,env))) e2
and eval_fun v1 v2 = match v1 with
  | Closure (x,e,env) -> eval (update env x v2) e
  | Rclosure (f,x,e,env) -> eval (update (update env f v1) x v2) e
  | _ -> failwith "function: Closure value expected"



type const   = BCON of bool | ICON of int
type token   = LP | RP | EQ | COL | ARR | ADD | SUB | MUL | LEQ
             | IF | THEN | ELSE | LAM | LET | IN | REC
             | CON of const | VAR of string | BOOL | INT

let code = Char.code
let num c = code c - code '0'
let digit c = code '0' <= code c && code c <= code '9'
let lc_letter c = code 'a' <= code c && code c <= code 'z'
let uc_letter c = code 'A' <= code c && code c <= code 'Z'
let whitespace c = match c with
  | ' ' | '\n' |  '\t' |'\r' -> true
  | _ -> false


let lex s : token list =
  let get i = String.get s i in
  let getstr i n = String.sub s (i-n) n in
  let exhausted i = i >= String.length s in
  let verify i c = not (exhausted i) && get i = c in
  let rec lex i l =
    if exhausted i then List.rev l
    else match get i with
      | '+' -> lex (i+1) (ADD::l)
      | '-' -> if verify (i+1) '>' then lex (i+2) (ARR::l) 
          else lex (i+1) (SUB::l)
          
      | '*' -> if verify (i+1) ')' then failwith "unmatched comment" 
          else lex (i+1) (MUL::l)
      | '<' -> if verify (i+1) '=' then lex (i+2) (LEQ::l)
          else failwith "lex: '=' expected" 
      | '=' ->lex (i+1) (EQ::l)
      | ')' ->lex (i+1) (RP::l)
      | '(' -> if verify (i+1) '*' then lex_comment (i+2) l 1 
          else lex (i+1) (LP::l) 
      |':' -> lex (i+1) (COL::l)
      | c when whitespace c -> lex (i+1) l
      | c when digit c -> lex_num (i+1) (num c) l
      | c when lc_letter c -> lex_id (i+1) 1 l
      | c -> failwith "lex: illegal character"
  and lex_comment i l openc =
    if openc =0 then lex i l 
    else if exhausted i then failwith "unmatched comment" 
    else match get i with 
      | '*' when verify (i+1) ')' ->  lex_comment (i+2) l (openc-1)
      | '(' when verify (i+1) '*'->   lex_comment (i+2) l (openc+1) 
      | _ -> lex_comment (i+1) l openc
  and lex_num i n l = if exhausted i then lex_num' i n l 
    else let c = get i in 
      if digit c then lex_num (i+1) ( n*10 + num c) l
      else lex_num' i n  l 
  and lex_num' i n l = lex i (CON (ICON n)::l)
  and lex_id i n l = 
    if exhausted i then lex_id' i n l
    else match get i with
      | '\'' | '_' -> lex_id (i+1) (n+1) l
      | c -> if lc_letter c || uc_letter c || digit c
          then lex_id (i+1) (n+1) l
          else lex_id' i n l 
  and lex_id' i n l = match getstr i n with
    | "if" -> lex i (IF::l)
    | "then" -> lex i (THEN::l)
    | "else" -> lex i (ELSE::l)
    | "fun" -> lex i (LAM::l)
    | "let" -> lex i (LET::l)
    | "in" -> lex i (IN::l)
    | "rec" -> lex i (REC::l)
    | "false" -> lex i (CON (BCON false)::l)
    | "true" -> lex i (CON (BCON true)::l)
    | "bool" -> lex i (BOOL::l)
    | "int" -> lex i (INT::l)
    | s -> lex i (VAR s::l)
  in lex 0 []

let verify c l =  match l with
  | [] -> failwith "verify: no token"
  | c'::l -> if c'=c then l else failwith "verify: wrong token"

let rec exp l : exp * token list = match l with
  | IF::l ->
      let (e1,l) = exp l in
      let (e2,l) = exp (verify THEN l) in
      let (e3,l) = exp (verify ELSE l) in
      (If(e1,e2,e3), l)
  | LAM::VAR x::ARR::l ->
      let (e,l) = exp l in (Lam (x,e), l)
  |LAM::LP::VAR x::COL :: l->let (t1,l) = ty l in 
      let (e,l) = exp (verify ARR (verify RP l) ) in (Lamty (x,t1,e),l)
  | LET::VAR x::EQ::l ->
      let (e1,l) = exp l in
      let (e2,l) = exp (verify IN l) in
      (Let (x,e1,e2), l)
  | LET::REC::VAR f::VAR x::EQ::l ->
      let (e1,l) = exp l in
      let (e2,l) = exp (verify IN l) in
      (Letrec (f,x,e1,e2), l)
  |LET::REC::VAR f::LP::VAR x ::COL::l -> let (t1,l) = ty l in
      let (t2,l) = ty (verify COL (verify RP l) ) in 
      let (e1,l) = exp (verify EQ l) in 
      let (e2,l) = exp (verify IN l) in
      (Letrecty (f,x,t1,Arrow(t1,t2),e1,e2),l)
      
  | l -> cexp l
and ty l = let (t1,l) = pty l in ty' t1 l
and ty' t1 l = 
  match l with 
  |ARR::l-> let (t2,l) = pty l in
      let (t3,l) = ty' t2 l in 
      (Arrow (t1,t3),l)
  |_-> (t1,l) 
and pty l = match l with 
  |BOOL ::l -> (Bool,l)
  |INT ::l-> (Int,l)
  |LP:: l -> let (t1,l) = ty l in (t1,(verify RP l)) 
  |_->failwith "Parsing type"
  
and cexp l = let (e,l) = sexp l in cexp' e l
and cexp' e1 l = match l with
  | LEQ::l -> let (e2,l) = sexp l in (Oapp(Leq,e1,e2), l)
  | l -> (e1,l)
and sexp l = let (e,l) = mexp l in sexp' e l
and sexp' e1 l = match l with
  | ADD::l -> let (e2,l) = mexp l in sexp' (Oapp(Add,e1,e2)) l
  | SUB::l -> let (e2,l) = mexp l in sexp' (Oapp(Sub,e1,e2)) l
  | l -> (e1,l)
and mexp l = let (e,l) = aexp l in mexp' e l
and mexp' e1 l = match l with
  | MUL::l -> let (e2,l) = aexp l in aexp' (Oapp(Mul,e1,e2)) l
  | l -> (e1,l)
and aexp l = let (e,l) = pexp l in aexp' e l
and aexp' e1 l = match l with
  | CON _ :: _ | VAR _ :: _ | LP :: _  ->
      let (e2,l) = pexp l in aexp' (Fapp(e1,e2)) l
  | l -> (e1,l)
and pexp l = match l with
  | CON (BCON b)::l -> (Con (Bcon b), l)
  | CON (ICON n)::l -> (Con (Icon n), l)
  | VAR x::l -> (Var x, l)
  | LP::l -> let (e,l) = exp l in (e, verify RP l)
  |  _ -> failwith "parsing experssion"

let checkStr s = check empty (fst(exp( lex s ) ))
let evalStr s = eval empty (fst(exp( lex s ) )) 































