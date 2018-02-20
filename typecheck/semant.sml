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
                val atl = actual_ty tyLeft
                val atr = actual_ty tyRight
        in
        case oper of
              (A.EqOp | A.NeqOp) => (
                checkIntsStrsRecsArrs(atl, atr, pos)
                )
            | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) => (
                checkIntsOrStrings(atl, atr, pos)
                )

            | (A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp) => (
                checkInts(atl, atr, pos)
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

and transLetExp(tenv, venv, var) =
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
        Types.INT (* TODO *)
  | transVarExp(tenv, venv, A.SubscriptVar(var, exp, pos)) =
        Types.INT (* TODO *)

(*******************************************************)

and transDecs(tenv, venv, decs) =
        let
        in {te=tenv, ve=venv}
        end

and transTy tenv ty =
        let
        in {}
        end

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
