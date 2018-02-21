structure A = Absyn
structure S = Symbol

structure Translate = struct type exp = unit end

structure Semant =
struct

type expty = {exp: Translate.exp, ty: Types.ty}

datatype envent = VarEnt of Types.ty
                | FunEnt of { params: Types.ty list, res: Types.ty }


(********************************************************)
(* Function for translating a NAME into a different     *)
(* type                                                 *)
fun actual_ty ty =
        case ty
         of Types.NAME ty' => actual_ty(Types.NAME ty')
          | ty' => ty'

(********************************************************)
(* Walk through a Record's field list, looking for      *)
(* symbol 'id2'. If it's in the list, return it's type. *)
(* If not, return Types.INT.                            *)

fun findFieldType(Types.RECORD((id1, ty)::rest, u), id2, pos) =
        if id1 = id2 then actual_ty ty
        else findFieldType(Types.RECORD(rest, u), id2, pos)
  | findFieldType(Types.RECORD([], u), id2, pos) =
        (ErrorMsg.error pos ("Unable to find symbol " ^
                                S.name id2 ^
                                " in record");
         Types.INT
        )

(********************************************************)
(* These functions are used to check the left and       *)
(* right sides of arithmetic operations.                *)

fun checkInts(Types.INT, Types.INT, _) =
        ()
  | checkInts(_, _, pos) =
        (ErrorMsg.error pos "integer operands required";
        ())

fun checkIntsOrStrings(Types.INT, Types.INT, _) =
        ()
  | checkIntsOrStrings(Types.STRING, Types.STRING, _) =
        ()
  | checkIntsOrStrings(_, _, pos) =
        (ErrorMsg.error pos "integer or string operands required";
        ())

fun checkIntsStrsRecsArrs(Types.INT, Types.INT, _) =
        ()
  | checkIntsStrsRecsArrs(Types.STRING, Types.STRING, _) =
        ()
  | checkIntsStrsRecsArrs(Types.RECORD(_, u1), Types.RECORD(_, u2), pos) =
        (if u1 = u2 then ()
         else
                (ErrorMsg.error pos "record types don't match";
                ())
        )
  | checkIntsStrsRecsArrs(Types.ARRAY(_, u1), Types.ARRAY(_, u2), pos) =
        (if u1 = u2 then ()
         else
                (ErrorMsg.error pos "array types don't match";
                ())
        )
  | checkIntsStrsRecsArrs(_, _, pos) =
        (ErrorMsg.error pos "integer, string, array, or record operands required";
        ())

(*******************************************************)

fun transOpExp(tenv, venv, A.OpExp{left, oper, right, pos}) =
        let
                val {exp=_, ty=tyLeft} = transExp(tenv, venv, left)
                val {exp=_, ty=tyRight} = transExp(tenv, venv, right)
                (* val atl = actual_ty tyLeft
                val atr = actual_ty tyRight *)
        in
        case oper of
              (A.EqOp | A.NeqOp) => (
                checkIntsStrsRecsArrs(tyLeft, tyRight, pos)
                )
            | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) => (
                checkIntsOrStrings(tyLeft, tyRight, pos)
                )

            | (A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp) => (
                checkInts(tyLeft, tyRight, pos)
                )
        end

(*******************************************************)

and transCallExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transRecordExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transSeqExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transAssignExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transIfExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transWhileExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transForExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transBreakExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transArrayExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transVarExp(tenv, venv, A.SimpleVar(id,pos)) =
        (case Symbol.look(venv, id)
         of SOME (VarEnt ty) => actual_ty ty
          | NONE => (ErrorMsg.error pos ("undefined variable " ^
                                                S.name id);
                        Types.INT)
        )
  | transVarExp(tenv, venv, A.FieldVar(var, id, pos)) =
        (case transVarExp(tenv, venv, var)
         of Types.RECORD record => (findFieldType(Types.RECORD record, id, pos))
          | _ => (ErrorMsg.error pos "Accessing a field in non-record type";
                        Types.INT)
        )
  | transVarExp(tenv, venv, A.SubscriptVar(var, exp, pos)) =
        (case transVarExp(tenv, venv, var)
         of Types.ARRAY(arrty, unique) => (
                let val {exp, ty=tyexp} = transExp(tenv, venv, exp)
                in
                  case tyexp
                    of Types.INT => (actual_ty arrty)
                     | _ => (ErrorMsg.error pos "Array index must be of type INT";
                                  Types.INT)
                end
                )
          | _ => (ErrorMsg.error pos "Accessing subscript of non-array type";
                        Types.INT)
        )

(*******************************************************)

and transVarDec(tenv, venv, A.VarDec{name, escape, typ, init, pos}) =
        let val {exp=(), ty=tyexp} = transExp(tenv, venv, init)
        in
        case typ
         of SOME(id, p) => (
                case Symbol.look(tenv, id)
                 of SOME typ =>
                        if (typ) = (tyexp) then
                                {te=tenv, ve=S.enter(venv, name, VarEnt tyexp)}
                        else (  ErrorMsg.error p "type mismatch";
                                {te=tenv, ve=venv}
                        )
                  | NONE => (   ErrorMsg.error p "type not defined";
                                {te=tenv, ve=venv}
                        )
                )
          | NONE => {te=tenv, ve=S.enter(venv, name, VarEnt tyexp)}
        end

and transFunDec(tenv, venv, []) =
        {te=tenv, ve=venv}
  | transFunDec(tenv, venv, {name, params, result, body, pos}::fundecs) =
        {te=tenv, ve=venv} (* TODO *)

and transTypDec(tenv, venv, []) =
        {te=tenv, ve=venv}
  | transTypDec(tenv, venv, {name, ty, pos}::typedecs) =
        {te=tenv, ve=venv} (* TODO *)

and transDecs(tenv, venv, A.FunctionDec dec::decs) =
        let val {te=tenv', ve=venv'} = transFunDec(tenv, venv, dec)
        in transDecs(tenv', venv', decs) end
  | transDecs(tenv, venv, A.VarDec dec::decs) =
        let val {te=tenv', ve=venv'} = transVarDec(tenv, venv, A.VarDec dec)
        in transDecs(tenv', venv', decs) end
  | transDecs(tenv, venv, A.TypeDec dec::decs) =
        let val {te=tenv', ve=venv'} = transTypDec(tenv, venv, dec)
        in transDecs(tenv', venv', decs) end
  | transDecs(tenv, venv, []) =
        {te=tenv, ve=venv}

(*******************************************************)

and transExp(tenv, venv, exp) =
case exp of
  A.OpExp opexp =>
        (transOpExp(tenv, venv, A.OpExp opexp);
        {exp=(), ty=Types.INT})
| A.VarExp var =>
        {exp=(), ty=transVarExp(tenv, venv, var)}
| A.NilExp =>
        {exp=(), ty=Types.NIL}
| A.IntExp n =>
        {exp=(), ty=Types.INT}
| A.StringExp(str, p) =>
        {exp=(), ty=Types.STRING}
| A.CallExp callexp =>
        {exp=(), ty=transCallExp(tenv, venv, A.CallExp callexp)}
| A.RecordExp recexp =>
        {exp=(), ty=transRecordExp(tenv, venv, recexp)}
| A.SeqExp seqexp =>
        {exp=(), ty=transSeqExp(tenv, venv, seqexp)}
| A.AssignExp assignexp =>
        {exp=(), ty=transAssignExp(tenv, venv, assignexp)}
| A.IfExp ifexp =>
        {exp=(), ty=transIfExp(tenv, venv, ifexp)}
| A.WhileExp whilexp =>
        {exp=(), ty=transWhileExp(tenv, venv, whilexp)}
| A.ForExp forexp =>
        {exp=(), ty=transForExp(tenv, venv, forexp)}
| A.BreakExp breakexp =>
        {exp=(), ty=transBreakExp(tenv, venv, breakexp)}
| A.LetExp {decs, body, pos} =>
        let val {te=tenv', ve=venv'} =
                        transDecs(tenv, venv, decs)
        in transExp(tenv', venv', body)
        end
| A.ArrayExp arrexp =>
        {exp=(), ty=transArrayExp(tenv, venv, arrexp)}

(*******************************************************)

and transProg(exp) =
        let
                val tenv : Types.ty Symbol.table = Symbol.empty
                val venv : envent Symbol.table = Symbol.empty

                (* add base environment *)
                val tenv = Symbol.enter(tenv, Symbol.symbol "string", Types.STRING);
                val tenv = Symbol.enter(tenv, Symbol.symbol "int", Types.INT);

                val venv = Symbol.enter(venv, Symbol.symbol "print",    FunEnt {params=[Types.STRING], res=Types.UNIT});
                val venv = Symbol.enter(venv, Symbol.symbol "flush",    FunEnt {params=[], res=Types.UNIT});
                val venv = Symbol.enter(venv, Symbol.symbol "getchar",  FunEnt {params=[], res=Types.STRING});
                val venv = Symbol.enter(venv, Symbol.symbol "ord",      FunEnt {params=[Types.STRING], res=Types.INT});
                val venv = Symbol.enter(venv, Symbol.symbol "chr",      FunEnt {params=[Types.INT], res=Types.STRING});
                val venv = Symbol.enter(venv, Symbol.symbol "size",     FunEnt {params=[Types.STRING], res=Types.INT});
                val venv = Symbol.enter(venv, Symbol.symbol "substring",FunEnt {params=[Types.STRING, Types.INT, Types.INT], res=Types.STRING});
                val venv = Symbol.enter(venv, Symbol.symbol "concat",   FunEnt {params=[Types.STRING, Types.STRING], res=Types.STRING});
                val venv = Symbol.enter(venv, Symbol.symbol "not",      FunEnt {params=[Types.INT], res=Types.INT});
                val venv = Symbol.enter(venv, Symbol.symbol "exit",     FunEnt {params=[Types.INT], res=Types.UNIT});
        in
                PrintAbsyn.print(TextIO.stdOut, Parse.parse "test1.tig");
                (* recurse *)
                ()
        end
end
