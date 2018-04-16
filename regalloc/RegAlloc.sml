signature REG_ALLOC =
sig
    structure Frame : FRAME
    val allocation : Frame.register Temp.Table.table
    val alloc : Assem.instr list * Frame.frame -> Assem.instr list * allocation

end
structure RegAlloc : REG_ALLOC = struct

    structure Frame = MipsFrame
    type allocation = Frame.register Temp.Table.table
    

    fun alloc (instrs, frame) =
        (*live analysis *) 
        let
            val (flowGraph, nodeList) = MakeGraph.instrs2graph instrs
            val (igraph, _) = Liveness.interferenceGraph flowGraph
            val (allocation, spillList) = Color.color {
                                                      interference=igraph,
                                                      initial=Frame.tempMap,
                                                      spillCost= (fn n:Graph.node => 1),
                                                      registers=Frame.registers
                                                      }                  
        in
           (allocation, spillList)
        end    
end


