(* Q11 : basic type inference *)

type myType = T_Int | T_Bool | T_Fun of myType * myType | T_Var of int

type binOp = OpPlus | OpTimes
 
type unOp = OpIsZero

type expr = Int of int
	| Bool of bool
	| Var of string
	| Fun of string * expr
	| App of expr * expr
	| If of expr * expr * expr
	| BinOp of binOp * expr * expr
	| UnOp of unOp * expr

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
		| T_Var i ->
			try
				List.assoc i sub
			with Not_found -> t
;;

(* 
Returns a funtor which excepts a context (Gamma) and apply the substitution to
the context, i.e. signma Gamma.
*)
let subContext sub =
	List.map
	(fun typ_typExpr_pair ->
		let (typ, typExpr) = typ_typExpr_pair in
		(typ, subSingle sub typExpr)
	)
;;

let rec occurs i t =
	match t with
		| T_Bool -> false
		| T_Int -> false
		| T_Var k -> i = k
		| T_Fun (t1, t2) -> (occurs i t1) || (occurs i t2)
;;

(* sub1 = sigma, sub2 = gamma *)
let rec subCompose sub1 sub2 =
	List.map
	(fun pair ->
		let (tv, te) = pair in
		(tv, subSingle sub1 te)
	)
	sub2
	@
	List.filter (fun x -> let (dom,_) = x in not (List.mem_assoc dom sub2)) sub1
;;

let rec unify s t =
	match s, t with
		| (T_Bool, T_Bool) -> []
		| (T_Int, T_Int) -> []
		| (T_Var i, T_Var j) -> if i = j then [] else [(i, t)]
		| (T_Var i, _) -> if occurs i t then raise (Fail "circularity") else [(i,t)]
		| (_, T_Var i) -> if occurs i s then raise (Fail "circularity") else [(i,s)]
		| (T_Fun (s1, s2), T_Fun (t1, t2)) ->
				let sub1 = unify s1 t1 in
				let sub2 = unify (subSingle sub1 s2) (subSingle sub1 t2) in
				subCompose sub2 sub1
		| _ -> raise (Fail "mismatch")
;;

let rec typeExprHelper expr context =
	match expr with
		| Int _ -> (T_Int, [])
		| Bool _ -> (T_Bool, [])
		| Var name ->
				(try
					(List.assoc name context, [])
				with Not_found -> raise (Fail "unbound"))
		| Fun (varName, fexpr) ->
			let fresh = freshTVar() in
			let (fType, sub) = typeExprHelper fexpr ((varName, fresh) :: context) in
			(T_Fun (subSingle sub fresh, fType), sub)
		| App (f, x) ->
			let (fType, sub1) = typeExprHelper f context in
			let (xType, sub2) = typeExprHelper x (subContext sub1 context) in
			let fresh = freshTVar() in
			let uleft = subSingle sub2 fType in
			let uright = T_Fun (xType, fresh) in
			let sub3 = unify uleft uright in
			let sub321 = subCompose sub3 (subCompose sub2 sub1) in
			(subSingle sub3 fresh, sub321)
		| BinOp (OpPlus, x1, x2) | BinOp (OpTimes, x1, x2) ->
			let (x1Type, sub1) = typeExprHelper x1 context in
			let (x2Type, sub2) = typeExprHelper x2 (subContext sub1 context) in
			let sub3 = unify x2Type x1Type in
			let sub4 = unify x1Type T_Int in
			let sub4321 = subCompose sub4 (subCompose sub3 (subCompose sub2 sub1)) in
			(T_Int, sub4321)
		| UnOp (OpIsZero, x) ->
			let (xType, sub1) = typeExprHelper x context in
			let sub2 = unify xType T_Int in
			(T_Bool, sub2)
		| If (cond, texpr, fexpr) ->
			let (condType, sub1) = typeExprHelper cond context in
			let sub2 = unify condType T_Bool in
			let (texprType, sub3) = typeExprHelper texpr (subContext sub2 context) in
			let (fexprType, sub4) = typeExprHelper fexpr (subContext sub3 context) in
			let sub5 = unify (subSingle sub4 texprType) (subSingle sub3 fexprType) in
			let sub54321 = subCompose sub5 (subCompose sub4 (subCompose sub3 (subCompose sub2 sub1))) in
			(subSingle sub5 texprType, sub54321)
;;

let typeExpr expr =
	resetTVar(); (* reset the counter for the second use *)
	let (t, _) = typeExprHelper expr [] in
	t
;;

(* ---------------------- Test cases ---------------------- *)
(*
#trace typeExprHelper
#trace unify
#trace subSingle
*)

assert(typeExpr (Int 123) = T_Int);;
assert(typeExpr (Fun ("x", Int 123)) = T_Fun (T_Var 1, T_Int));;
assert(typeExpr (Fun ("x", Var "x")) = T_Fun (T_Var 1, T_Var 1));;
assert(typeExpr (Fun ("x", Bool true)) = T_Fun (T_Var 1, T_Bool));;
assert(typeExpr (Fun ("x", Fun ("y", Var "y"))) = T_Fun (T_Var 1, T_Fun (T_Var 2, T_Var 2)));;
assert(typeExpr (Fun ("x", Fun ("y", Var "x"))) = T_Fun (T_Var 1, T_Fun (T_Var 2, T_Var 1)));;
assert(typeExpr (App (Fun ("x", Var "x"), Int 3)) = T_Int);;
assert(typeExpr (App (Fun ("x", Bool true), Int 3)) = T_Bool);;
assert(typeExpr (App (Fun ("x", Var "x"), Fun ("x", Var "x"))) = T_Fun (T_Var 2, T_Var 2));;
assert(typeExpr (App (Fun ("x", Var "x"), App (Fun ("v", Var "v"), Int 123))) = T_Int);
assert(typeExpr (App (Fun ("x", Var "x"), App (Fun ("v", Fun ("x", Var "x")), Int 123))) = T_Fun (T_Var 3, T_Var 3));;
assert(typeExpr (App (Fun ("x", Fun ("y", Var "x")), Int 123)) = T_Fun (T_Var 2, T_Int));;
assert(typeExpr (App (Fun ("x", App (Var "x", Int 123)), Fun ("y", Var "y"))) = T_Int);;
assert(typeExpr (App (Fun ("x", App (Var "x", Int 123)), Fun ("y", Bool true))) = T_Bool);;
assert(typeExpr (App (Fun ("x", App (Var "x",  Fun ("y", Bool true))), Fun ("y", Bool true))) = T_Bool);;
assert(typeExpr (App (Fun ("x", App (Var "x",  Fun ("z", Bool true))), Fun ("y", Var "y"))) = T_Fun (T_Var 2, T_Bool));;
assert(typeExpr (Fun ("y", Fun ("x", App (Var "x", Var "y")))) = T_Fun (T_Var 1, T_Fun (T_Fun (T_Var 1, T_Var 3), T_Var 3)));;

assert(typeExpr (App (Fun ("x", App (Var "x", Int 123)), Fun ("y", Var "y"))) = T_Int);;

let assert_fail expr reason =
	try
		let impossible = typeExpr expr
		in assert (impossible != impossible)  (* UNREACHABLE *)
	with
		| Fail cause -> assert(cause = reason)
;;

let assert_unbound expr = assert_fail expr "unbound";;
let assert_circularity expr = assert_fail expr "circularity";;
let assert_mismatch expr = assert_fail expr "mismatch";;

assert_mismatch (App (Int 3, Int 3));;
assert_mismatch (App ((App (Fun ("x", Var "x"), Int 3)), Int 3));;
assert_mismatch(Fun ("x", App (App (Fun ("y", Var "y") , Int 3), Var "x")));;

assert_unbound (Fun ("x", Var "y"));;
assert_unbound (App (Fun ("x", Var "x"), App (Fun ("v", Var "x"), Int 123)));

assert_circularity (Fun ("x", App (Var "x", Var "x")));;
assert_circularity (Fun ("x", App (App (Var "x", Int 3), Var "x")));;
assert_circularity (Fun ("x", App (App (Fun ("y", Var "y") , Var "x"), Var "x")));;

(* Q12 tests *)
typeExpr (UnOp (OpIsZero, Int 123333)) ;;
assert(typeExpr (UnOp (OpIsZero, Int 123333)) = T_Bool);;
assert(typeExpr (UnOp (OpIsZero, (App (Fun ("x", App (Var "x", Int 123)), Fun ("y", Var "y"))))) = T_Bool);;
assert(typeExpr (App ((Fun ("x", Var "x")), (UnOp (OpIsZero, Int 123333)))) = T_Bool);;
assert(typeExpr (Fun ("x", UnOp (OpIsZero, Var "x"))) = T_Fun (T_Int, T_Bool));;

assert(typeExpr (BinOp (OpPlus, Int 123333, Int 123)) = T_Int);;
assert(typeExpr (BinOp (OpTimes, Int 123333, Int 123)) = T_Int);;
assert(typeExpr (BinOp (OpPlus, Int 123, (App (Fun ("x", App (Var "x", Int 123)), Fun ("y", Var "y"))))) = T_Int);;
assert(typeExpr (Fun ("x", Fun ("y", BinOp (OpPlus, Var "x", Var "y")))) = T_Fun (T_Int, T_Fun (T_Int, T_Int)));;
assert(typeExpr (App ((Fun ("x", Fun ("y", BinOp (OpPlus, Var "x", Var "y")))), Int 123)) = T_Fun (T_Int, T_Int));;
assert(typeExpr (App ((App ((Fun ("x", Fun ("y", BinOp (OpPlus, Var "x", Var "y")))), Int 123)), Int 123)) = T_Int);;

assert_mismatch(UnOp (OpIsZero, Bool true));;
assert_mismatch(UnOp (OpIsZero, (App (Fun ("x", App (Var "x", Bool true)), Fun ("y", Var "y")))));;
assert_mismatch(BinOp (OpTimes, Bool true, Int 123));;
assert_mismatch(BinOp (OpPlus, Int 123, (App (Fun ("x", App (Var "x", Bool true)), Fun ("y", Var "y")))));;

assert(typeExpr (If (Bool true, Bool true, Bool true)) = T_Bool);;
assert(typeExpr (If (Bool true, Int 1, Int 2)) = T_Int);;
assert(typeExpr (Fun ("x", If (Var "x", Int 1, Int 1))) = T_Fun(T_Bool, T_Int));;
assert(typeExpr (If (Bool true, Fun ("x", Var "x"), Fun ("x", If (Var "x", Var "x", Var "x")))) = T_Fun(T_Bool, T_Bool));;
assert(typeExpr (App ((If (Bool true, Fun ("x", Var "x"), Fun ("x", If (Bool true, Var "x", Var "x")))), Bool true)) = T_Bool);;
assert(typeExpr (App ((If (Bool true, Fun ("x", Var "x"), Fun ("x", If (Bool true, Var "x", Var "x")))), Int 3)) = T_Int);;

assert_mismatch(Fun ("x", If (Var "x", Int 1, Bool true)));;
assert_mismatch(App ((If (Bool true, Fun ("x", Var "x"), Fun ("x", If (Bool true, Var "x", Int 2)))), Bool true));;

assert_unbound (App ((If (Bool true, Fun ("x", Var "x"), Fun ("x", If (Var "y", Var "x", Var "x")))), Int 3));;
