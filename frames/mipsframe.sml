structure MipsFrame : FRAME =
struct

        structure T = Tree
        structure A = Assem

        datatype access = InFrame of int | InReg of Temp.temp

        type frame = {  label: Temp.label,      (* machine code label *)
                        formals: access list,   (* location of variables *)
                        nextOffset: int ref,    (* next stack offset    *)
                        parent: int,
                        (* other things *)
                        prologue: Tree.stm
                        }

        datatype frag = PROC of {body: Tree.stm, frame: frame}
                      | STRING of Temp.label * string

        val wordSize = 4

        type register = string
       

        (* registers *)

        val FP = Temp.newtemp() 
        val SP = Temp.newtemp()
        val RV = Temp.newtemp()
        val RA = Temp.newtemp()

        val a0 = Temp.newtemp()
        val a1 = Temp.newtemp()
        val a2 = Temp.newtemp()
        val a3 = Temp.newtemp()

        val t0 = Temp.newtemp()
        val t1 = Temp.newtemp()
        val t2 = Temp.newtemp()
        val t3 = Temp.newtemp()
        val t4 = Temp.newtemp()
        val t5 = Temp.newtemp()
        val t6 = Temp.newtemp()
        val t7 = Temp.newtemp()
        val t8 = Temp.newtemp()
        val t9 = Temp.newtemp()
       
        val s0 = Temp.newtemp()
        val s1 = Temp.newtemp()
        val s2 = Temp.newtemp()
        val s3 = Temp.newtemp()
        val s4 = Temp.newtemp()
        val s5 = Temp.newtemp()
        val s6 = Temp.newtemp()
        val s7 = Temp.newtemp()        


        val specialregs = [RV,FP,SP,RA]

        val argregs = [a0, a1, a2, a3]

        val calleesaves = [s0,s1,s2,s3,s4,s5,s6,s7]

        val callersaves = [t0,t1,t2,t3,t4,t5,t6,t7,t8,t9]

        val tempMap =
          let       
             val regList = [(RV, "RV"), (SP, "SP"),(FP, "FP"),(RA, "RA"),
                             (a0, "a0"), (a1, "a1"), (a2, "a2"), (a3, "a3"),
			     (s0, "s0"), (s1, "s1"), (s2, "s2"), (s3, "s3"), (s4, "s4"), (s5, "s5"), (s6, "s6"), (s7, "s7"),
			     (t0, "t0"), (t1, "t1"), (t2, "t2"), (t3, "t3"), (t4, "t4"), (t5, "t5"), (t6, "t6"), (t7, "t7"), (t8, "t8"), (t9, "t9")]
             fun enterTable ((reg, name), table) = Temp.Table.enter(table, reg, name)
          in  
             List.foldr enterTable Temp.Table.empty regList
          end
        
        val registers = IntBinaryMap.listItems(tempMap)

        fun makeString temp =
          case Temp.Table.look (tempMap, temp) of
              SOME str => str
              | NONE => Temp.makestring temp     

        fun string(lab, s) = (Symbol.name lab) ^ ": .ascii \"" ^ s ^"\" \n"
  
        fun formals(f:frame) = #formals f

        fun name(f: frame) = #label f

        fun exp (acc:access) (e : Tree.exp) = 
	    case acc
	     of InFrame off => Tree.MEM (Tree.BINOP (Tree.PLUS, e, Tree.CONST off))
              | InReg reg =>  Tree.TEMP reg
    

        fun newFrame{name: Temp.label,
                        formals: bool list,
                        parent: int}: frame =
                let val off = ref wordSize
                    fun formals2acc(_, []) = []
                      | formals2acc(off, f :: flist) =
                         let val acc = if f then (off := !off - wordSize;
                                                 InFrame(!off))
                                       else (print "\tAllocating new temp for parameter\n";
                                                InReg(Temp.newtemp()))
                         in acc :: formals2acc(off, flist)
                         end
                    val forms = formals2acc(off, formals)

                    fun genPrologue([], _) = Tree.MOVE(Tree.TEMP FP, Tree.TEMP FP)
                      | genPrologue(acc :: accList, i) =
                          let val src = if i < 4 then
                                                Tree.TEMP(List.nth(argregs, i))
                                        else
                                                Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP FP, Tree.CONST (i* wordSize)))
                          in Tree.SEQ(Tree.MOVE(exp (acc) (Tree.TEMP FP), src),
                                   genPrologue(accList, i+1)
                                )
                          end

                in { label=name,
                     formals=forms,
                     nextOffset=off,
                     parent=parent,
                     prologue = genPrologue(forms, 0)}
                end

        fun allocLocal (f: frame) (esc: bool) =
                let val off = #nextOffset f
                in if esc then
                        (off := !off - wordSize;
                        InFrame(!off))
                   else InReg(Temp.newtemp())
                end

       
        fun externalCall (s, args) =
            Tree.CALL(Tree.NAME(Temp.namedlabel s), args)

        fun procEntryExit1(frame: frame, body: Tree.stm) =
                let (* 1. allocLocal for every callee saves register? *)
                    fun createCalleeTemps([]) =
                            [Temp.newtemp(), Temp.newtemp()]    (* allocate one for RA, FP *)
                      | createCalleeTemps(cs::calleesaves) =
                            Temp.newtemp() :: createCalleeTemps(calleesaves)

                    val calleeTemps = createCalleeTemps(calleesaves)

                    fun saveCallee(tempRA :: tempFP :: [], [], t: Tree.stm) =
                        T.SEQ(T.MOVE(T.TEMP tempFP, T.TEMP FP),
                                T.SEQ(T.MOVE(T.TEMP tempRA, T.TEMP RA),
                                        t))
                      | saveCallee(temp::tempList, cs::calleeSaves, t: Tree.stm) =
                        T.SEQ(T.MOVE(T.TEMP temp, T.TEMP cs),
                                saveCallee(tempList, calleeSaves, t))

                    fun restoreCallee(tempRA :: tempFP :: [], [], t: Tree.stm) =
                        T.SEQ(t,
                                T.SEQ(T.MOVE(T.TEMP FP, T.TEMP tempFP),
                                        T.MOVE(T.TEMP RA, T.TEMP tempRA)))
                      | restoreCallee(temp::tempList, cs::calleeSaves, t: Tree.stm) =
                        T.SEQ(restoreCallee(tempList, calleeSaves, t),
                                T.MOVE(T.TEMP cs, T.TEMP temp))

                    val newBody = restoreCallee(calleeTemps, calleesaves,
                                        saveCallee(calleeTemps, calleesaves, body))

                in T.SEQ( #prologue frame, newBody )
                end
        
        fun procEntryExit2 (frame,body) =
           body @
               [Assem.OPER{assem="",
                src=[RA,SP,FP]@calleesaves,
                dst=[],jump=SOME[]}]

        fun procEntryExit3(frame:frame, instrs) =
          let val prolog = Symbol.name(#label frame) ^ "\n"
              val epilog = "\n"

                (* functions to manipulate SP *)
              fun allocSP (instrs) =
                      A.OPER{
                                assem = "addi `s0, `s0, "^ Int.toString(!(#nextOffset frame))
                                                ^"\n",
                                dst = [SP],
                                src = [SP],
                                jump = NONE } :: instrs
              fun deallocSP (instrs) =
                instrs @ [
                        A.OPER{ assem = "addi `s0, `s0, " ^
                                                Int.toString(~1 * !(#nextOffset frame))
                                                ^"\n",
                                dst = [SP],
                                src = [SP],
                                jump = NONE
                                }
                        ]
              fun return(instrs) =
                instrs @
                        [A.OPER{ assem = "jr $ra\n",
                                src = [RA],
                                dst = [],
                                jump = NONE }
                        ]

                fun label(instrs) =
                        A.LABEL{
                                assem = Symbol.name(#label frame) ^ ":\n",
                                lab = #label frame
                        } :: instrs

                (* 1. allocate space on the stack *)
                (* 2. save callee-save and return address registers *)
                (* 3. body *)
                (* 4. load callee-save and return address registers *)
                (* 5. deallocate stack pointer *)
                (* 6. jump return *)
              val body = label(return(
                                deallocSP(
                                allocSP(instrs))))
          in {prolog=prolog, body=body, epilog=epilog}
          end
end

structure Frame = MipsFrame
