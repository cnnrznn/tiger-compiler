structure A = Absyn

structure Translate = struct type exp = unit end

structure Semant =
struct

type expty = {exp: Translate.exp, ty: Types.ty}

datatype envent = VarEnt of Types.ty
                | FunEnt of { params: Types.ty list, res: Types.ty }

(*******************************************************)

fun compareFieldLists([], []) = true (* same length, or empty *)
  | compareFieldLists((s1,t1)::f1, (s2,t2)::f2) =
        (t1 = t2)
  | compareFieldLists(_, _) = false (* different lengths *)

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
  | checkIntsStrsRecsArrs(Types.RECORD(fl1, _), Types.RECORD(fl2, _), pos) =
        (if compareFieldLists(fl1, fl2) then ()
         else
                (ErrorMsg.error pos "record types don't match";
                ())
        )
  | checkIntsStrsRecsArrs(Types.ARRAY(t1, _), Types.ARRAY(t2, _), pos) =
        (if t1 = t2 then ()
         else
                (ErrorMsg.error pos "array types don't match";
                ())
        )
  | checkIntsStrsRecsArrs(_, _, pos) =
        (ErrorMsg.error pos "integer, string, array or record operands required";
        ())

(*******************************************************)

fun transOp(tenv, venv, A.OpExp{left=lexp, oper=mop, right=rexp, pos=p}) =
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

and transVar(tenv, venv, var) =
        let
        in {}
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
        (transOp(tenv, venv, A.OpExp opexp);
        {exp=(), ty=Types.INT})
| A.VarExp var =>
        {exp=(), ty=Types.INT}
| A.NilExp =>
        {exp=(), ty=Types.INT}
| A.StringExp(str, p) =>
        {exp=(), ty=Types.INT}
| A.CallExp callexp =>
        {exp=(), ty=Types.INT}
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
