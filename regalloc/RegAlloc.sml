signature REG_ALLOC =
sig
    structure Frame : FRAME
    type allocation
    val alloc : Assem.instr list * Frame.frame -> Assem.instr list * allocation

end
structure RegAlloc : REG_ALLOC = struct

    structure Frame = MipsFrame
    structure T = Tree
    structure A = Assem
    type allocation = Frame.register Temp.Table.table
    

    fun alloc (instrs, frame) =
        (*live analysis *) 
        let
            val (flowGraph, nodeList) = MakeGraph.instrs2graph instrs
            val (igraph, fgTempMap) = Liveness.interferenceGraph flowGraph
             (**** Debugging purposes ****)
            (* val dummy = (TextIO.output(TextIO.stdOut, "\n\n====== Liveout for Control Flow Graph node info =========\n\n");
                         List.app (fn n =>  let val temps = List.foldr (fn (t,l) => l ^ (Frame.makeString t) ^ " ," ) "" (fgTempMap n)
                                            in TextIO.output( TextIO.stdOut,  ((Graph.nodename n) ^":  "^ temps ^ "\n") )
                                            end) (Graph.nodes (#control flowGraph)) ;
                         TextIO.output(TextIO.stdOut, "\n\n====== Liveout for Control Flow Graph node info- END =========\n\n") ) *)
           
            val (color_alloc, spillNodes) = Color.color {
                                                      interference=igraph,
                                                      initial=Frame.tempMap,
                                                      spillCost= (fn n:Graph.node => 1),
                                                      registers=Frame.registers
                                                      }    

          
                  fun rewriteProgram(node:: nodes, allInstrs) =
                      let 
                          val acc = Frame.allocLocal (frame) (true)  

                          fun gen_instrs(t, srcList, dstList) =
                              if ( List.exists (fn l => t = l ) (srcList@dstList) ) then
                                 let 
                                     val newT = Temp.newtemp()
                                     val isLoad = List.exists (fn l => t = l ) (srcList)
                                     val isStore = List.exists (fn l => t = l ) (dstList)
                                     val load_instrs =  if isLoad then
                                                           MipsGen.codegen (frame) (T.MOVE(T.TEMP newT, Frame.exp (acc) (T.TEMP Frame.FP) ))
                                                        else []
                                     val store_instrs = if isStore then 
                                                            MipsGen.codegen (frame) (T.MOVE(Frame.exp (acc) (T.TEMP Frame.FP), T.TEMP newT))
                                                        else []
                                     fun get_newList (oldList) =
                                        List.map (fn (l) => if t = l then newT else l) oldList 
                                 in 
                                    
                                    (load_instrs, store_instrs, get_newList (srcList), get_newList (dstList))
                                 end
                                    
                              else
                                  ([],[],srcList, dstList) 
                            
                          fun rewritePerSpill (node, first :: rest) =
                             let val newInstrs = (case first of
                                                    A.OPER{assem=assem, src=src, dst=dst,jump=jump} => let val (load_instrs, store_instrs, newSrc, newDst)   = gen_instrs(node, src, dst)
                                                                                    
                                                                                    in 
                                                                                        load_instrs @ [ A.OPER{assem=assem, src= newSrc, dst= newDst, jump=jump}] @ store_instrs
                                                                                    end
                                                    |A.LABEL{assem=_, lab=lab} => [first]

                                                    |A.MOVE {assem=assem, src=src, dst=dst} => let val (load_instrs, store_instrs, newSrc, newDst)  = gen_instrs(node, [src], [dst])
                                                                       in
                                                                           load_instrs @ [A.MOVE{assem=assem, src= (List.hd newSrc), dst= (List.hd newDst)}] @ store_instrs
                                                                       end  )  
                             in newInstrs @ rewritePerSpill(node, rest)
                             end
                           |rewritePerSpill (node, []) = []
                          
                      in 
                         let val newInstrs = rewritePerSpill (node, allInstrs )
                         in  rewriteProgram(nodes, newInstrs)
                         end
                      end
                    | rewriteProgram([], allInstrs) = allInstrs
        
             fun isDupMove(instr) =
                  case instr of
                     A.MOVE {assem = assem, src = src, dst=dst} => 
                        let val srcReg = case Temp.Table.look(color_alloc, src) of 
                                         SOME r => r
                                         |NONE => (ErrorMsg.error 0 "fatal in remove Dup moves"; "")
                            val dstReg = case Temp.Table.look(color_alloc, dst) of 
                                         SOME r => r
                                         |NONE => (ErrorMsg.error 0 "fatal in remove Dup moves"; "")
                        in
                             if String.compare(srcReg, dstReg) = EQUAL then
                                  true
                             else 
                                  false
                        end  
                     | _ => false
                      
             
                             
        in
            
           case spillNodes of
             [] => let val newInstrs = List.filter (fn i => not(isDupMove i)) instrs  in (newInstrs, color_alloc) end
             |temps => ( let val newAssemInstrs = rewriteProgram (spillNodes, instrs) in  alloc(newAssemInstrs, frame) end)
            
        end    
end


