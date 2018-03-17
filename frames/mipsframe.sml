structure MipsFrame : FRAME =
struct

        datatype access = InFrame of int | InReg of Temp.temp

        type frame = {  label: Temp.label,      (* machine code label *)
                        formals: access list,   (* location of variables *)
                        nextOffset: int ref     (* next stack offset    *)
                        (* other things *)
                        }
        val wordSize = 4
        val FP = Temp.newTemp()
        fun formals(f:frame) = #formals f

        fun name(f: frame) = #label f

        fun newFrame{name: Temp.label,
                        formals: bool list}: frame =
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
                     nextOffset=off }
                end

        fun allocLocal (f: frame) (esc: bool) =
                let val off = #nextOffset f
                in if esc then
                        (off := !off - wordSize;
                        InFrame(!off))
                   else InReg(Temp.newtemp())
                end

        fun exp (acc:access) (e : Tree.exp) = 
	    case access 
	     of InFrame off => (Tree.MEM (Tree.BINOP (Tree.PLUS, e, Tree.CONST off)))
                |InReg reg =>  (Tree.TEMP reg)  

end

structure Frame = MipsFrame
