signature CODEGEN =
sig
    structure Frame: FRAME
    val codegen : Frame.frame -> Tree.stm -> Assem.instr list
end

structure MipsGen : CODEGEN = struct
  
   structure Frame = MipsFrame
   structure A = Assem
   structure T = Tree

   
   fun codegen (frame)(stm : Tree.stm) =
   let val ilist = ref (nil: A.instr list)
       fun emit x = ilist := x:: !ilist
       fun result (gen) = 
           let val t = Temp.newtemp() 
           in gen t ; t 
           end

        fun toMipsStr T.EQ = "beq"
          | toMipsStr T.NE = "bne"
          | toMipsStr T.LT = "blt"
          | toMipsStr T.GT = "bgt"
          | toMipsStr T.LE = "ble"
          | toMipsStr T.GE = "bge"
  
       fun toMipsStr_z T.EQ = "beqz"
          | toMipsStr_z T.NE = "bnez"
          | toMipsStr_z T.LT = "bltz"
          | toMipsStr_z T.GT = "bgtz"
          | toMipsStr_z T.LE = "blez"
          | toMipsStr_z T.GE = "bgez"


       fun munchStm(T.SEQ (a,b)) = (munchStm a; munchStm b)
           (* store instructions *)
           | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2)) = 
		emit(A.OPER {assem = "sw `s1 , "^ Int.toString i ^ "(`s0) \n", src = [munchExp e1, munchExp e2], dst = [], jump = NONE }) 

           | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)), e2)) =
		emit(A.OPER {assem = "sw `s1 , "^ Int.toString i ^ "(`s0) \n", src = [munchExp e1, munchExp e2], dst = [], jump = NONE })

           | munchStm (T.MOVE(T.MEM(e1) , e2)) =
		emit(A.OPER {assem = "sw `s1 , (`s0) \n", src = [munchExp e1, munchExp e2], dst = [], jump = NONE })

           (* load instructions *) 
           | munchStm(T.MOVE(T.TEMP r, T.CONST i)) = 
		emit(A.OPER {assem = "li `d0, " ^ Int.toString i ^ "\n",src = [], dst = [r], jump = NONE})

           | munchStm(T.MOVE(T.TEMP r, T.NAME lab )) = 
                emit( A.OPER {assem="la `d0, " ^ Symbol.name lab ^ "\n", src=[], dst=[r], jump=NONE})

           | munchStm( T.MOVE(T.TEMP r, T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)))) = 
                emit( A.OPER {assem="lw `d0, " ^ Int.toString i ^ "(`s0)\n", src=[munchExp e1], dst=[r], jump=NONE})

           | munchStm(T.MOVE(T.TEMP r, T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)))) = 
                emit( A.OPER {assem="lw `d0, " ^ Int.toString i ^ "(`s0)\n", src=[munchExp e1], dst=[r], jump=NONE})

           | munchStm (T.MOVE(T.TEMP r, e)) =
                emit(A.MOVE {assem= "move `d0, `s0 \n", src = munchExp e , dst = r})

           | munchStm (T.LABEL lab) =
		emit(A.LABEL {assem= Symbol.name lab ^ ":\n", lab=lab}) (*doubt: is label always followed by a colon?*)

           | munchStm(T.JUMP(T.NAME lab , lablist)) =
                emit( A.OPER {assem="j " ^ Symbol.name lab ^ "\n", src=[], dst=[], jump=SOME(lablist)})
 
           | munchStm(T.JUMP(e, lablist)) =
                emit( A.OPER {assem="jr `s0\n", src=[munchExp e], dst=[], jump=SOME(lablist)})
           
           | munchStm (T.CJUMP(relop, e, T.CONST 0, l1, l2)) =
            	emit(A.OPER{assem= (toMipsStr_z relop) ^ " `s0, `j0\nb `j1 \n", dst=[],src=[munchExp e ],jump=SOME [l1,l2]}) (* should we add this case at all *)

           | munchStm(T.CJUMP(relop, e1, e2, l1, l2)) = 
		emit(A.OPER {assem= (toMipsStr relop) ^ "`s0, `s1, `j0 \n b `j1 \n", src=[munchExp e1, munchExp e2], dst=[], jump=SOME [l1, l2]})

           | munchStm(T.EXP (T.CALL(T.NAME (n), args))) =
                let
                    val calldefs = Frame.RV :: Frame.RA ::Frame.callersaves
                in 
		    emit(A.OPER {assem = "jal `s0\n", src = munchExp(T.NAME (n)) :: munchArgs(0,n, args, List.length (args)) , dst= calldefs , jump=NONE}) (*incomplete *)
                end
           | munchStm (T.EXP e)= (munchExp e; ())

           (* mem load expressions *)
       and munchExp(T.MEM(T.BINOP(T.PLUS, e, T.CONST i))) =
		result(fn r => emit(A.OPER {assem = "lw `d0, " ^ Int.toString i ^ "(`s0)\n", src=[munchExp e], dst=[r], jump=NONE }))

           | munchExp(T.MEM(T.BINOP(T.PLUS,T.CONST i, e))) =
		result(fn r => emit(A.OPER {assem = "lw `d0, " ^ Int.toString i ^ "(`s0)\n", src=[munchExp e], dst=[r], jump=NONE }))

           | munchExp(T.MEM(T.CONST i)) =
		result(fn r => emit(A.OPER{ assem="lw `d0, " ^ Int.toString i ^ "\n", src=[] , dst=[r] , jump=NONE}))

           | munchExp (T.MEM e) =
            	result(fn r => emit(A.OPER{ assem="lw `d0, 0(`s0) \n", src=[munchExp e] , dst=[r] , jump=NONE}))
	   
            (* arithmetic expressions *)

	   | munchExp(T.BINOP(T.PLUS, e, T.CONST i)) =
               result(fn r => emit( A.OPER {assem="addi `d0, `s0, " ^ Int.toString i ^ "\n", src=[munchExp e], dst=[r], jump=NONE}))

           | munchExp(T.BINOP(T.PLUS, T.CONST i, e)) =
               result(fn r => emit( A.OPER {assem="addi `d0, `s0, " ^ Int.toString i ^ "\n", src=[munchExp e], dst=[r], jump=NONE}))

           | munchExp(T.BINOP(T.MINUS, e, T.CONST i)) =
               result(fn r => emit( A.OPER {assem="addi `d0, `s0, " ^ (Int.toString (~i)) ^ "\n", src=[munchExp e], dst=[r], jump=NONE}))

           | munchExp(T.BINOP(T.PLUS, e1, e2)) =
               result(fn r => emit( A.OPER {assem="add `d0, `s0, `s1\n", src=[munchExp e1, munchExp e2], dst=[r], jump=NONE} ))

           | munchExp(T.BINOP(T.MINUS, e1, e2)) =
              result(fn r => emit( A.OPER {assem="sub `d0, `s0, `s1\n", src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))
           
           | munchExp(T.BINOP(T.MUL, e1, e2)) =
              result(fn r => emit( A.OPER {assem="mulo `d0, `s0, `s1\n", src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

          | munchExp(T.BINOP(T.DIV, e1, e2)) =
              result(fn r => emit( A.OPER {assem="div `d0, `s0, `s1\n", src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

	   | munchExp(T.CONST i) =
                result(fn r => emit( A.OPER {assem="li `d0," ^ Int.toString i ^ "\n",src=[] , dst=[r], jump=NONE}))

           | munchExp (T.NAME n) =
      		result(fn r => emit(A.OPER {assem="la `d0, " ^ Symbol.name n ^ "\n" , src=[] , dst=[r], jump=NONE}))

           | munchExp(T.TEMP t) = t
           | munchExp(T.CALL(T.NAME (n), args)) =
                let
                    val calldefs = Frame.RV :: Frame.RA :: Frame.callersaves
                in 
		    emit(A.OPER {assem = "jal  `s0 \n", src = munchExp(T.NAME (n))::munchArgs(0,n, args, List.length (args)) , dst= calldefs , jump=NONE});
                    Frame.RV
                end

        and munchArgs( i ,n, arg::rest, num_args ) = 
                
  	       ( if i = 0 then
                    munchStm(T.MOVE(T.TEMP Frame.SP, T.BINOP(T.MINUS, T.TEMP Frame.SP, T.CONST (num_args * Frame.wordSize))))  
                 else () ;
                           
                 if i < 4 then
                     let val reg = List.nth(Frame.argregs, i)
                     in munchStm(T.MOVE( T.TEMP reg , arg )) ;
                        [reg] @ munchArgs(i+1,n, rest, num_args)
                     end                  
                 else
                   (munchStm(T.MOVE(T.MEM(T.BINOP(T.MINUS, T.TEMP Frame.SP, T.CONST (i * Frame.wordSize))) , arg));
                    nil @ munchArgs(i+1,n, rest, num_args)
                    )
                  
                 )
                 
            | munchArgs(i ,n, [], num_args ) =  ( munchStm(T.MOVE(T.TEMP Frame.FP, T.TEMP Frame.SP))
                                        ; [])

   in munchStm stm;
      rev (!ilist)
   end

end

