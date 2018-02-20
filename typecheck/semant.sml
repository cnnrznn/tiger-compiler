structure A = Absyn

structure Translate = struct type exp = unit end

structure Semant =
struct

type expty = {exp: Translate.exp, ty: Types.ty}

datatype envent = VarEnt of Types.ty
                | FunEnt of { params: Types.ty list, res: Types.ty }

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
        (ErrorMsg.error pos "integer, string, array or record operands required";
        ())

(*******************************************************)

fun transOpExp(tenv, venv, A.OpExp{left=lexp, oper=mop, right=rexp, pos=p}) =
        let
                val {exp=_, ty=tyLeft} = transExp(tenv, venv, lexp)
                val {exp=_, ty=tyRight} = transExp(tenv, venv, rexp)
        in
        case mop of
              (A.EqOp | A.NeqOp) => (
                checkIntsStrsRecsArrs(tyLeft, tyRight, p)
                )
            | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) => (
                checkIntsOrStrings(tyLeft, tyRight, p)
                )

            | (A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp) => (
                checkInts(tyLeft, tyRight, p)
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

and transVarExp(tenv, venv, var) =
        let
        in Types.INT
        end

(*******************************************************)

and transDec(tenv, venv, dec) =
        let
        in {}
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
| A.LetExp letexp =>
        {exp=(), ty=transLetExp(tenv, venv, letexp)}
| A.ArrayExp arrexp =>
        {exp=(), ty=transArrayExp(tenv, venv, arrexp)}
(* TODO fill in rest of expression types *)

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
