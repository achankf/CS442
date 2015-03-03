open List;;

(* Q11 : basic type inference *)

type myType = T_Int | T_Bool | T_Fun of myType * myType | T_Var of int

type expr = Int of int
	| Bool of bool
	| Var of string
	| Fun of string * expr
	| App of expr * expr

type subst = (int * myType) list

exception Fail of string

let count = ref 0

(* permitted mutation *)

let freshTVar() = T_Var (count := !count+1; !count)

let resetTVar() = count := 0

(* end of permitted mutation *)
;;

let rec subSingle sub t =
	match t with
		| T_Int -> T_Int
		| T_Bool -> T_Bool
		| T_Fun (t1, t2) -> T_Fun(subSingle sub t1, subSingle sub t2)
		| T_Var i ->  assoc (T_Var i) sub
;;

(* 
Returns a funtor which excepts a context (Gamma) and apply the substitution to
the context, i.e. signma Gamma.
*)
let subContext sub =
	map
	(fun var_type_pair ->
		let (var, varType) = var_type_pair in
		(var, subSingle sub varType)
	)
;;

let rec typeExprHelper expr context =
	match expr with
		| Int _ -> (T_Int, [])
		| Bool _ -> (T_Bool, [])
		| Var name -> (assoc name context, [])
		| Fun (varName, fexpr) ->
			let fresh = freshTVar() in
			let (fType, sub) = typeExprHelper fexpr ((varName, fresh) :: context) in
			(T_Fun (fresh, fType), sub)
		| App (f, x) ->
			let (fType, sub1) = typeExprHelper f context in
			let context_sub1 = subContext sub1 context in
			let (xType, sub2) = typeExprHelper x context in
			(fType, [])
;;

let rec unify t1 t2 =
	[]
;;

let typeExpr expr =
	resetTVar(); (* reset the counter for the second use *)
	typeExprHelper expr [];;

assert(typeExpr (Int 123) = (T_Int, []));;
assert(typeExpr (Fun ("x", Int 123)) = (T_Fun (T_Var 1, T_Int), []));;
assert(typeExpr (Fun ("x", Var "x")) = (T_Fun (T_Var 1, T_Var 1), []));;
assert(typeExpr (Fun ("x", Bool true)) = (T_Fun (T_Var 1, T_Bool), []));;
assert(typeExpr (Fun ("x", Fun ("y", Var "y"))) = (T_Fun (T_Var 1, T_Fun (T_Var 2, T_Var 2)), []));;
assert(typeExpr (Fun ("x", Fun ("y", Var "x"))) = ((T_Fun (T_Var 1, T_Fun (T_Var 2, T_Var 1)),[])));;

typeExpr (App (Fun ("x", Var "x"), Int 3));;
