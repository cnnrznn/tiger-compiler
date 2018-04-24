signature FRAME =
sig 
        type frame
        type access
        type register

        val newFrame : {name: Temp.label,
                       formals: bool list,
                       parent: int}
                       -> frame
        val name : frame -> Temp.label
        val formals : frame -> access list
        val allocLocal : frame -> bool -> access
     
        val FP: Temp.temp
        val RV: Temp.temp
        val RA: Temp.temp 
        val SP: Temp.temp

        (* function argument registers *)
        val a0: Temp.temp
        val a1: Temp.temp
        val a2: Temp.temp
        val a3: Temp.temp
          
        (* caller saved registers *)
        val t0 : Temp.temp
        val t1 : Temp.temp 
        val t2 : Temp.temp
        val t3 : Temp.temp
        val t4 : Temp.temp
        val t5 : Temp.temp
        val t6 : Temp.temp
        val t7 : Temp.temp
        val t8 : Temp.temp
        val t9 : Temp.temp

        (* callee saved registers *)

        val s0 : Temp.temp
        val s1 : Temp.temp 
        val s2 : Temp.temp
        val s3 : Temp.temp
        val s4 : Temp.temp
        val s5 : Temp.temp
        val s6 : Temp.temp
        val s7 : Temp.temp
        
        val specialregs : Temp.temp list
        val argregs : Temp.temp list
        val callersaves : Temp.temp list
        val calleesaves : Temp.temp list   
       
        val tempMap : register Temp.Table.table
        val registers : register list
        val makeString : Temp.temp -> register
        val string: Temp.label * string -> string

        val wordSize : int
        val exp: access -> Tree.exp -> Tree.exp
        val externalCall: string * Tree.exp list -> Tree.exp

        val procEntryExit1: frame * Tree.stm -> Tree.stm
        val procEntryExit2: frame * Assem.instr list -> Assem.instr list
        val procEntryExit3: frame * Assem.instr list ->
                { prolog: string,
                  body: Assem.instr list,
                  epilog: string }

        datatype frag = PROC of {body: Tree.stm, frame: frame}
                      | STRING of Temp.label * string
end
