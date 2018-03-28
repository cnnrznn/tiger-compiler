structure MipsFrame : FRAME =
struct

        datatype access = InFrame of int | InReg of Temp.temp

        type frame = {  label: Temp.label,      (* machine code label *)
                        formals: access list,   (* location of variables *)
                        nextOffset: int ref,    (* next stack offset    *)
                        parent: int
                        (* other things *)
                        }

        datatype frag = PROC of {body: Tree.stm, frame: frame}
                      | STRING of Temp.label * string

        val wordSize = 4

        type register = string
        val tempMap (*incomplete*)

        (* registers *)

        val FP = Temp.newtemp() 
        val SP = Temp.newtemp()
        val RV = Temp.newtemp()
        val RA = Temp.newtemp()
        
        val specialargs = [RV,FP,SP,RA]

        val argregs = []

        val calleesaves = []

        val callersaves = []

        fun formals(f:frame) = #formals f

        fun name(f: frame) = #label f

        fun newFrame{name: Temp.label,
                        formals: bool list,
                        parent: int}: frame =
                let val off = ref wordSize
                    fun formals2acc(_, []) = []
                      | formals2acc(off, f :: flist) =
                         let val acc = if f then (off := !off - wordSize;
                                                 InFrame(!off))
                                       else InReg(Temp.newtemp())
                         in acc :: formals2acc(off, flist)
                         end
                in { label=name,
                     formals=formals2acc(off, formals),
                     nextOffset=off,
                     parent=parent}
                end

        fun allocLocal (f: frame) (esc: bool) =
                let val off = #nextOffset f
                in if esc then
                        (off := !off - wordSize;
                        InFrame(!off))
                   else InReg(Temp.newtemp())
                end

        fun exp (acc:access) (e : Tree.exp) = 
	    case acc
	     of InFrame off => Tree.MEM (Tree.BINOP (Tree.PLUS, e, Tree.CONST off))
              | InReg reg =>  Tree.TEMP reg
    
        fun externalCall (s, args) =
            Tree.CALL(Tree.NAME(Temp.namedlabel s), args)

        fun procEntryExit1(frame: frame, body: Tree.stm) = body

end

structure Frame = MipsFrame
