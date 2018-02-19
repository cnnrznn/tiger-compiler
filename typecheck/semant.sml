structure Translate = struct type exp = unit end

structure Semant =
struct

type expty = {exp: Translate.exp, ty: Types.ty}

datatype envent = VarEnt of Types.ty
                | FunEnt of { params: Types.ty list, res: Types.ty }

(*******************************************************)

fun checkInts Types.INT Types.INT _ =
        ()
  | checkInts _ _ pos =
        (ErrorMsg.error pos "integer operands required";
        ())

fun checkIntsOrStrings Types.INT Types.INT _ =
        ()
  | checkIntsOrStrings Types.STRING Types.STRING _ =
        ()
  | checkIntsOrStrings _ _ pos =
        (ErrorMsg.error pos "integer or string operands required";
        ())

fun checkSame tl tr pos =
        if tl = tr then
                ()
        else
                (ErrorMsg.error pos "type mismatch";
                ())

(*******************************************************)

fun transOp(tenv, venv, Absyn.OpExp{left=lexp, oper=mop, right=rexp, pos=p}) =
        let
                val {exp=_, ty=tyLeft} = transExp(tenv, venv, lexp)
                val {exp=_, ty=tyRight} = transExp(tenv, venv, rexp)
        in
        (*case mop of
              (Absyn.ExOp | Absyn.NeqOp) => (
                checkSame(tyLeft, tyRight)
                )
            | (Absyn.LtOp | Absyn.LeOp | Absyn.GtOp | Absyn.GeOp) => (
                checkIntsOrStrings(tyLeft, tyRight)
                )

            | (Absyn.PlusOp | Absyn.MinusOp | Absyn.TimesOp | Absyn.DivideOp) => (
                checkInts(tyLeft, tyRight, p)
                )*)
                ()
        end

(*******************************************************)

fun transVar tenv venv var =
        let
        in {}
        end

(*******************************************************)

fun transDec tenv venv dec =
        let
        in {}
        end

(*******************************************************)

fun transExp tenv venv exp =
case exp of
  Absyn.OpExp opexp =>
        (transOp(tenv, venv, Absyn.OpExp opexp);
        {exp=(), ty=Types.INT})
| Absyn.VarExp var =>
        {exp=(), ty=Types.INT}
| Absyn.NilExp =>
        {exp=(), ty=Types.INT}
| Absyn.StringExp(str, p) =>
        {exp=(), ty=Types.INT}
| Absyn.CallExp callexp =>
        {exp=(), ty=Types.INT}
(* TODO fill in rest of expression types *)

(*******************************************************)

fun transProg exp =
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
