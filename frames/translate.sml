signature TRANSLATE =
sig
	type level
	type access (* not the same as Frame.access *)

	val outermost : level
	val newLevel : {parent: level, name: Temp.label,
	    	       	formals: bool list} -> level
	val formals: level -> access list
	val allocLocal: level -> bool -> access

        val init : unit -> unit

        datatype exp = Ex of Tree.exp
                     | Nx of Tree.stm
                     | Cx of Temp.label * Temp.label -> Tree.stm

        val unEx: exp -> Tree.exp
        val unNx: exp -> Tree.stm
        val unCx: exp -> Temp.label * Temp.label -> Tree.stm

        val procEntryExit: {level: level, bodyExp: exp} -> unit

        val getResult: unit -> Frame.frag list

        val simpleVar: access * level -> exp
        val subscriptVar : exp * exp -> exp
        val fieldVar: exp * int -> exp
        val binop: A.oper * exp * exp -> exp
        val whileExp: Temp.label * Temp.label *
                        Temp.label *exp * exp
                        -> exp
        val forExp: exp * exp * exp * exp * Temp.label -> exp
        val ifThenElse: exp * exp * exp -> exp
        val ifThen: exp * exp -> exp
        val recordExp: exp list -> exp
        val arrayExp : exp * exp -> exp
        val callExp: level * level * Temp.label * exp list -> exp
        val strExp: string -> exp
        val assignment: access * exp * level -> exp
        val break: Temp.label option -> exp
        val intExp: int -> exp
        val nilExp: unit -> exp
        val assignExp: exp * exp -> exp
        val seqExp: exp list * exp -> exp

        val prepend: exp list * exp -> exp

        val errorTree: int -> exp

        val printTree: exp -> unit
end

structure Translate : TRANSLATE =
struct
        (*type level = {parent : level, frame : Frame.frame, unique : unit ref}*)
        type level = int
        type access = level * Frame.access

        datatype exp = Ex of Tree.exp
             | Nx of Tree.stm
             | Cx of Temp.label * Temp.label -> Tree.stm

        val outermost = 0
        val nextLevel = ref 0

        val fragList: Frame.frag list ref = ref []

        (********************************************************)
        (* The Translate struct has a ref hash table for     *)
        (* mapping levels (ints) to frames. This is useful      *)
        (* for "walking" up from a child level to a parent      *)
        (* level, for allocating local variables, etc.          *)

        structure Table = IntMapTable(type key=level
                                fun getInt level = level)
        val HT : Frame.frame Table.table ref = ref Table.empty

        fun init () =
                let val frame = Frame.newFrame{name=Temp.newlabel(), formals=[],
                                                parent= ~1}
                    val HT' = Table.enter(!HT, outermost, frame)
                in HT := HT'
                end
        (********************************************************)

        fun newLevel{parent=plev, name: Temp.label, formals: bool list} =
                let val frame = Frame.newFrame{name = name,
                                                formals = true :: formals,
                                                parent=plev}
                in nextLevel := !nextLevel + 1;
                   (* create mapping from nextLevel -> frame *)
                   HT := Table.enter(!HT, !nextLevel, frame);
                   !nextLevel
                end

        (********************************************************)
        (* Create a new access for a variable given the level   *)
        (* and a bool indicating whether the variable escapes   *)
        (* the current frame. If it doesn not (esc is false)    *)
        (* then allocate a Temp.temp. Otherwise, allocate       *)
        (* InFrame.                                             *)
        fun allocLocal (lev:level) (esc:bool) =
                let val frame = case Table.look(!HT, lev)
                                 of SOME f => f
                                  | NONE => (ErrorMsg.error 0 "should never see this";
                                                {label=Temp.newlabel(),
                                                 formals=[],
                                                 nextOffset=ref 4,
                                                 parent=outermost
                                                })
                    val acc = Frame.allocLocal(frame)(esc)
                in (lev, acc)
                end

        fun formals level =
                case Table.look(!HT, level)
                 of SOME frame => let fun makeList(_, []) = []
                                    | makeList(level, formal :: formals) =
                                        (level, formal) :: makeList(level, formals)
                              in makeList(level, #formals frame)
                              end
                  | NONE => (ErrorMsg.error 0 "should never see this";
                                [])


        structure T = Tree

        datatype exp = Ex of Tree.exp
                     | Nx of Tree.stm
                     | Cx of Temp.label * Temp.label -> Tree.stm

        fun unEx (Ex ex) = ex
          | unEx (Cx genstm) =
                let val r = Temp.newtemp()
                    val t = Temp.newlabel() and f = Temp.newlabel()
                in T.ESEQ(T.SEQ(T.MOVE(T.TEMP r, T.CONST 1),
                                T.SEQ(genstm(t,f),
                                      T.SEQ(T.LABEL f,
                                            T.SEQ(T.MOVE(T.TEMP r, T.CONST 0),
                                                  T.LABEL t)
                                            )
                                      )
                                ),
                                T.TEMP r)
                end
          | unEx (Nx nx) = T.ESEQ(nx, T.CONST 0)

        and unNx (Ex ex) = T.EXP(ex)
          | unNx (Cx genstm) =
                let val l = Temp.newlabel()
                in T.SEQ(genstm(l,l), T.LABEL l)
                end
          | unNx (Nx nx) = nx

        and unCx (Ex ex) =
                (fn (t, f) => T.CJUMP(T.NE, ex, T.CONST 0, t, f))
          | unCx (Cx genstm) = genstm
          | unCx (Nx nx) = (
                ErrorMsg.error 0 "Error using no-value statement in conditional";
                fn (t, f) => T.CJUMP(T.GT, T.CONST 0, T.CONST 1, t, f)
                )

        (************************************************)
        (* HELPER FUNCTIONS                             *)

        fun printTree(t: exp) = Printtree.printtree(TextIO.stdOut, unNx(t))

        fun prepend(explist: exp list, exp: exp) =
                let val ex = unEx(exp)
                    fun explist2stm(exp :: []) = unNx(exp)
                      | explist2stm(exp :: rest) =
                          T.SEQ(unNx exp, explist2stm(rest))
                in
                        case explist
                         of [] => Ex(ex)
                          | _ => Ex(T.ESEQ(explist2stm(explist), ex))
                end

        fun errorTree(n: int) = Ex(T.MEM(T.CONST n))

        fun procEntryExit{level: level, bodyExp: exp} =
                let val body = T.MOVE(T.TEMP Frame.RV, unEx bodyExp)
                in case Table.look(!HT, level)
                    of NONE => ErrorMsg.error 0 "catastrophic error"
                     | SOME f => fragList := Frame.PROC{body=body, frame=f} :: !fragList
                end

        fun getResult() = !fragList

        (*****************************************)
        (* function to translate simple variable *)

        fun simpleVarRec(acc: access, alev: int, t: T.exp) =
                let val dlev = #1 acc
                    val frAcc = #2 acc
                in
                        case Table.look(!HT, alev)
                         of NONE => (ErrorMsg.error 0 "could not find frame of variable"; Tree.MEM(T.CONST 0))
                          | SOME f => if dlev = alev
                                      then Frame.exp(frAcc)(t)
                                      else simpleVarRec(acc, #parent f, T.MEM(t))
                end

        fun simpleVar(acc : access, alev: level) =
                Ex(simpleVarRec(acc, alev, T.TEMP Frame.FP))
        
       fun subscriptVar(varExp: exp, indexExp: exp) =
          Ex( Tree.MEM( Tree.BINOP( Tree.PLUS, unEx varExp, Tree.BINOP( Tree.MUL,  unEx indexExp , Tree.CONST (Frame.wordSize) ) )))

       fun fieldVar (varExp : exp, fieldIndex : int) =
           Ex( Tree.MEM ( Tree.BINOP ( Tree.PLUS, unEx varExp , Tree.CONST(fieldIndex * Frame.wordSize) ) ) )

        fun binop(oper: A.oper, expl: exp, expr: exp) =
                let val exl = unEx(expl)
                    val exr = unEx(expr)
                in
                    case oper
                     of A.PlusOp =>
                                Ex(T.BINOP(T.PLUS, exl, exr))
                      | A.MinusOp =>
                                Ex(T.BINOP(T.MINUS, exl, exr))
                      | A.TimesOp =>
                                Ex(T.BINOP(T.MUL, exl, exr))
                      | A.DivideOp =>
                                Ex(T.BINOP(T.DIV, exl, exr))
                      | A.EqOp =>
                                Cx(fn(t,f) => T.CJUMP(T.EQ, exl, exr, t, f))
                      | A.NeqOp =>
                                Cx(fn(t,f) => T.CJUMP(T.NE, exl, exr, t, f))
                      | A.LtOp =>
                                Cx(fn(t,f) => T.CJUMP(T.LT, exl, exr, t, f))
                      | A.LeOp =>
                                Cx(fn(t,f) => T.CJUMP(T.LE, exl, exr, t, f))
                      | A.GtOp =>
                                Cx(fn(t,f) => T.CJUMP(T.GT, exl, exr, t, f))
                      | A.GeOp =>
                                Cx(fn(t,f) => T.CJUMP(T.GE, exl, exr, t, f))
                end

        fun whileExp(labDone: Temp.label, labBody: Temp.label, labTest: Temp.label,
                        expBody: exp, expTest: exp) =
                let
                        val exBod = unNx(expBody)
                        val exTest = unCx(expTest)
                in
                        Nx(T.SEQ(T.JUMP(T.NAME labTest, [labTest]),
                                 T.SEQ(T.LABEL labBody,
                                 T.SEQ(exBod,
                                 T.SEQ(T.LABEL labTest,
                                 T.SEQ(exTest(labBody, labDone), T.LABEL labDone))))))
                end

        fun forExp(expIndx: exp, expInit: exp, expHi: exp, expBody: exp,
                        labDone: Temp.label) =
                let val exHi = unEx(expHi)
                    val exLo = unEx(expInit)
                    val exBody = unNx(expBody)
                    val exIndx = unEx(expIndx)

                    val labBody = Temp.newlabel()
                    val labTest = Temp.newlabel()
                    val tempHi = Temp.newtemp()

                in  Nx(T.SEQ(T.MOVE(exIndx, exLo),
                       T.SEQ(T.MOVE(T.TEMP tempHi, exHi),
                       T.SEQ(T.LABEL labTest,
                       T.SEQ(T.CJUMP(T.LE, exIndx, T.TEMP tempHi, labBody, labDone),
                       T.SEQ(T.LABEL labBody,
                       T.SEQ(exBody,
                       T.SEQ(T.MOVE(exIndx, T.BINOP(T.PLUS, exIndx, T.CONST 1)),
                       T.SEQ(T.JUMP(T.NAME labTest, [labTest]), T.LABEL labDone))))))))
                    )
                end

        fun ifThenElse(expTest: exp, expThen: exp, expElse: exp) =
                let val exTest = unCx(expTest)
                    val exThen = unEx(expThen)
                    val exElse = unEx(expElse)
                    val labelThen = Temp.newlabel()
                    val labelElse = Temp.newlabel()
                    val labelDone = Temp.newlabel()
                    val r = Temp.newtemp()
                in
                        Ex(T.ESEQ(T.SEQ(exTest(labelThen, labelElse),
                                  T.SEQ(T.LABEL labelThen,
                                  T.SEQ(T.MOVE(T.TEMP r, exThen),
                                  T.SEQ(T.JUMP(T.NAME labelDone, [labelDone]),
                                  T.SEQ(T.LABEL labelElse,
                                  T.SEQ(T.MOVE(T.TEMP r, exElse),
                                  T.SEQ(T.JUMP(T.NAME labelDone, [labelDone]),
                                        T.LABEL labelDone))))))),
                                T.TEMP r))
                end
        fun ifThen(expTest: exp, expThen: exp) =
                let val exTest = unCx(expTest)
                    val exThen = unNx(expThen)
                    val labelThen = Temp.newlabel()
                    val labelDone = Temp.newlabel()
                in
                        Nx(T.SEQ(exTest(labelThen, labelDone),
                           T.SEQ(T.LABEL labelThen,
                           T.SEQ(exThen, T.LABEL labelDone))))
                end

        fun recursiveRecord(e::[], r, index) =
                T.MOVE(T.MEM(T.BINOP(T.PLUS,T.TEMP r, T.CONST(index * Frame.wordSize))), unEx e)
          | recursiveRecord(e::restList, r, index) =
                T.SEQ(T.MOVE(T.MEM(T.BINOP(T.PLUS,T.TEMP r, T.CONST(index * Frame.wordSize))), unEx e) , recursiveRecord(restList, r, index+1))
          | recursiveRecord(_, _, _) =
                T.EXP(T.MEM(T.CONST 0)) (* this is a real error condition *)

       (*| recursiveTrees([], r, index) = T.MEM(T.CONST 0) *) (* Oh so I guess inserting seg faults is normal compiler behavior? *)
        

       fun recordExp(fieldList) = 
           let val r = Temp.newtemp()
           in  Ex(T.ESEQ(
                        T.SEQ(T.MOVE(T.TEMP r, Frame.externalCall("initRecord", [T.CONST(Frame.wordSize * length fieldList  )])),
                              recursiveRecord(fieldList , r, 0)),
                        T.TEMP r))
           end

       fun arrayExp(sizeExp, initExp)=
           let val r = Temp.newtemp()
           in Ex( T.ESEQ( T.MOVE( T.TEMP r, Frame.externalCall ("initArray", [ unEx sizeExp, unEx initExp ])), T.TEMP r))
           end

       fun callExpRec(callerLev: int, funLev : int, t ) =
             case (Table.look(!HT, callerLev), Table.look(!HT, funLev))
              of (SOME callerFrame, SOME targetFrame) =>
                        if callerLev = #parent targetFrame
                        then t
                        else callExpRec(#parent callerFrame, funLev, T.MEM(t))
               | (_, _) => (ErrorMsg.error 0 "could not find frame of function"; T.MEM(T.CONST 0))

       fun callExp(funLevel, callerLevel, funLabel, argexps) =
           let val staticlink = callExpRec(callerLevel, funLevel, T.TEMP Frame.FP)
           in  Ex(T.CALL(T.NAME funLabel, staticlink:: List.map unEx argexps))
           end

        fun strExp(str: string) =
                let val label = Temp.newlabel()
                in  fragList := Frame.STRING(label, str) :: !fragList;
                    Ex(Tree.NAME label)
                end

        fun assignment(acc: access, expInit: exp, lev: level) =
                let val ex = unEx(expInit)
                in  Nx(T.MOVE(unEx(simpleVar(acc, lev)), ex))
                end

        fun break(label: Temp.label option) =
                case label
                 of NONE => errorTree(6)
                  | SOME l => Nx(T.JUMP(T.NAME l, [l]))

        fun intExp(x: int) = Ex(T.CONST x)

        fun nilExp() = Ex(T.CONST 0)

        fun assignExp(expVar: exp, expInit: exp) =
                let val exVar = unEx expVar
                    val exInit = unEx expInit
                in  Nx(T.MOVE(exVar, exInit))
                end

        fun seqExp(expList: exp list, expLast: exp) =
                let fun makeSeq([]) = T.EXP(T.CONST 0)
                      | makeSeq(exp :: []) = unNx exp
                      | makeSeq(exp :: om :: rest) = T.SEQ(unNx exp, makeSeq(om :: rest))
                    val seq = makeSeq(expList)
                in Ex(T.ESEQ(seq, unEx expLast))
                end
end
