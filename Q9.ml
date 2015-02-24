(* Q8 : basic type checking *)

type binOp = OpPlus | OpTimes

type unOp = OpIsZero

type myType = T_Int | T_Bool | T_Fun of myType * myType

type expr = Int of int
          | Bool of bool
          | If of expr * expr * expr
          | BinOp of binOp * expr * expr 
          | UnOp of unOp * expr 
          | Var of string
          | Fun of (string * myType) * expr
          | App of expr * expr
					| Let of (string * expr) * expr
					| Letrec of ((string * myType) * expr) * expr

exception Fail of string

let rec printList env =
	match env with
		| [] -> Printf.printf "\n"
		| (k,_)::xs -> Printf.printf "%s, " k; printList xs;
;;

let typeExpr expr =
	let rec typeExprHelper expr env =
		match expr with
		| Int _ -> T_Int
		| Bool _ -> T_Bool
		| If (cond, texpr, fexpr) ->
				if (typeExprHelper cond env) <> T_Bool
					then raise (Fail "not Boolean")
				else
					let texpr_type = (typeExprHelper texpr env) in 
					if texpr_type <> (typeExprHelper fexpr env) then raise (Fail "mismatch") else texpr_type
		| BinOp (binOp, left, right) ->
				let leftType = typeExprHelper left env in
				let rightType = typeExprHelper right env in
					(match binOp with
						| OpPlus -> if leftType = rightType then T_Int else raise (Fail "mismatch")
						| OpTimes -> if leftType = rightType then T_Int else raise (Fail "mismatch")
					)
		| UnOp (unOp, uexpr) ->
				let uexprType = typeExprHelper uexpr env in
					(match unOp with
						| OpIsZero -> if uexprType = T_Int then T_Bool else raise (Fail "mismatch")
					)
		| Fun ((varName, varType), fexpr) -> T_Fun (varType, typeExprHelper fexpr ((varName, varType):: env))
		| Let ((varName, varExpr), lexpr) -> typeExprHelper lexpr ((varName, typeExprHelper varExpr env) :: env)
		| App (f, x) ->
				let fType = typeExprHelper f env in
				let xType = typeExprHelper x env in
				(match fType with
					| T_Fun (argType, retType) -> if xType = argType then retType else raise (Fail "mismatch")
					| _ -> raise (Fail "not function")
				)
		| Letrec (((fName, fType), fExpr), inExpr) ->
				let fExprType = typeExprHelper fExpr ((fName, fType) :: env) in
				if fExprType <> fType then raise (Fail "mismatch")
				else typeExprHelper inExpr ((fName, fType) :: env)
		| Var x ->
				try
(*
					printList env;
					Printf.printf "Looking for %s\n" x;
*)
					List.assoc x env
				with
					| Not_found -> 
(*
						Printf.printf "%s not bound\n" x;
*)
						raise (Fail "not bound")
	in typeExprHelper expr []
;;

(* ----------------- Test Cases ----------------- *)

let assert_error expr =
	try
		let impossible = typeExpr expr
		in assert false && (impossible != impossible)  (* UNREACHABLE *)
	with
		| Fail _ -> true (* OKAY *)
;;

assert(typeExpr (Int 123) = T_Int);;
assert(typeExpr (Bool true) = T_Bool);;
assert(typeExpr (Bool false) = T_Bool);;
assert(typeExpr (UnOp (OpIsZero, Int 2312)) = T_Bool);;
assert(typeExpr (UnOp (OpIsZero, Int 0)) = T_Bool);;
assert(typeExpr (UnOp (OpIsZero, App(Fun (("x", T_Bool), Int 12333), Bool true))) = T_Bool);;
assert(typeExpr (UnOp (OpIsZero, App(Fun (("x", T_Bool), 
		App (Fun (("y", T_Bool), If (Var "y", Int 123, Int 222)), Var "x")
	), Bool true)))
	= T_Bool);;
assert(typeExpr (BinOp (OpPlus, App(Fun (("x", T_Bool), Int 12333), Bool true), Int 123)) = T_Int);;
assert(typeExpr (BinOp (OpTimes, App(Fun (("x", T_Bool), Int 12333), Bool true), Int 123)) = T_Int);;
assert(typeExpr (If (Bool true, Bool true, Bool true)) = T_Bool);;
assert(typeExpr (If (Bool true, Int 123, Int 234)) = T_Int);;
assert(typeExpr (Fun(("x", T_Bool), Var "x")) = T_Fun (T_Bool, T_Bool));;
assert(typeExpr (Fun(("x", T_Bool), If(Var "x", Bool true, Bool true))) = T_Fun (T_Bool, T_Bool));;
assert(typeExpr (App (Fun(("x", T_Bool), If(Var "x", Bool true, Bool true)), Bool true)) = T_Bool);;
assert(typeExpr (Let (("someBool", (App (Fun(("x", T_Bool), If(Var "x", Bool true, Bool true)), Bool true))), Var "someBool"))  = T_Bool);;
assert(typeExpr (Let (("x", If(Bool true, Bool true, Bool true)), (Var "x"))) = T_Bool);;
assert(typeExpr (Letrec ((("infinite", T_Fun (T_Int, T_Int)), Fun (("x", T_Int), App (Var "infinite", Var "x"))), App (Var "infinite", Int 0))) = T_Int);;

assert_error(If (Int 123, Bool true, Bool true));;
assert_error(Var "abc");;
assert_error(If (Bool true, Int 123, Bool true));;
assert_error(App (Fun(("x", T_Bool), If(Var "x", Bool true, Bool true)), Int 1234));;
assert_error(UnOp (OpIsZero, Bool true));;
assert_error(UnOp (OpIsZero, Fun (("x", T_Bool), Var "x")));;
assert_error(UnOp (OpIsZero, App(Fun (("x", T_Bool), Var "x"), Bool true)));;
assert_error(BinOp (OpPlus, Bool true, Int 123));;
assert_error(BinOp (OpTimes, Bool true, Int 123));;
assert_error(Let (("x", If(Bool true, Bool true, Bool true)), App ((Var "x"), Int 0)));;
typeExpr (Letrec ((("x", T_Fun(T_Int, T_Bool)), If(App(Var "x", Int 0), Bool true, Bool true)), App ((Var "x"), Int 0)));; 

assert(typeExpr (Let (("f1", Bool true), Let (("f1", Int 1), (Var "f1")))) = T_Int);;
