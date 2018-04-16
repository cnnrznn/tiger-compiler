signature COLOR =
sig 
    structure Frame: FRAME
    val allocation : Frame.register Temp.Table.table
    val color : { interference : Liveness.igraph,
                  initial : allocation,
                  spillCost : Graph.node -> int,
                  registers : Frame.register list} -> allocation * Temp.temp list
end 

structure Color : COLOR = struct


    structure RegSet = ListSetFn(
    type ord_key = string
    fun compare (r1,r2) = String.compare(r1,r2))


    structure Frame = MipsFrame
    type allocation = Frame.register Temp.Table.table
   
   
    fun color (Liveness.IGRAPH{graph=graph, tnode=tnode, gTemp=gTemp, moves = moves} , initPre , spillCost, registers ) =
    let
        (* all the workslists *)
        val simplifyWorkList = ref IntBinarySet.empty
        val spillWorkList = ref IntBinarySet.empty
        val moveWorkList = ref IntBinarySet.empty 
        val moveList = ref Graph.Table.empty
        val coloredNodes = ref IntBinarySet.empty
        val precoloredNodes = ref IntBinarySet.empty
        val initial = ref IntBinarySet.empty
        val spilledNodes = ref IntBinarySet.empty
        val selectStack : Graph.node list ref = ref []

        val degree = List.foldr (fn (n, t)  => Graph.Table.enter (!t, n, degreeof n)) ref Graph.Table.empty (Graph.nodes graph)
        val color = ref Graph.Table.empty
     
        fun degreeof (node) =
            List.length (Graph.adj(node))     
  
        fun buildprecolored()=
             List.app  ( fn ((t,r)) => let val n = tnode t
                                       in  (precoloredNodes := IntBinarySet.add(!precoloredNodes, n) ;
                                            color := Graph.Table.enter(!color, n,r))
                                       end ) ( IntBinaryMap.listItemsi(initPre)) 

       
        fun buildCI() =
           (* initialize initial structure*)
           List.app ( fn (node) => let val t = gTemp node
                                   in
                                      case Temp.Table.look(initPre, t) of
                                          SOME reg => coloredNodes :=  IntBinarySet.add(!coloredNodes, node) 
                                          | NONE  =>  initial := IntBinarySet.add(!initial, node)
                                   end )  Graph.nodes graph
        fun buildML() =
           (* make the moveList Table *)
           List.app (fn ( (n1,n2), t) => (t := Temp.Table.enter (!t, n1, n2); t := Temp.Table.enter (!t, n2, n1) )) moveList moves



        fun makeWorkList(node::nodes) = 
            let val k = List.length registers
            in 
              if Graph.Table.look (!degree, node) >= k then
                  spillWorkList := IntBinarySet.add(!spillWorkList, node)
              else
                  simplifyWorkList := IntBinarySet.add(!simplifyWorkList, node)
            end
           | makeWorkList([]) = ()

        fun decrementDegree(node) =
            let 
                val deg = case Graph.Table.look (!degree, node) of
                        SOME d => d
                        |NONE  => (ErrorMsg.error 0 "Error in decrementdegree" ; INT 0)
                val k = List.length registers
                 
            in
              degree := Graph.Table.enter(!degree, node, (deg-1)) ;
              if deg = k then
                  spillWorkList := IntBinarySet.delete(!spillWorkList, node)
                  simplifyWorkList := IntBinarySet.add(!simplifyWorkList, node)
              else ()
            end
           
        
        fun simplify(node :: nodes) =
           let
               val adjnodes = Graph.adj(node)
           in
              (simplifyWorkList := IntBinarySet.delete(!simplifyWorkList, node);
               selectStack := node :: !selectStack;
               List.app (fn n => decrementDegree n) adjnodes ;
               simplify(nodes) )
           end
            
            | simplify ([]) = ()
            
           
       fun assignColors(node) =
           let 
              val adjlist = Graph.adj node
              val okColors = RegSet.addList( RegSet.empty , registers)
              val u = IntBinarySet.union(!coloredNodes, !precoloredNodes)
           in
              let
                  val remColors = List.foldr (fn (a,c) => if IntBinarySet.member(u, a) then
                                                              RegSet.delete(c, Graph.Table.look(!color, a))
                                                          else c ) okColors adjlist
                                                          
              in 
                  if RegSet.isEmpty( remColors) then
                      spilledNodes := IntBinarySet.add(!spilledNodes, node)
                  else
                      coloredNodes := IntBinarySet.add(!coloredNodes, node)
                      color := Graph.Table.enter(!color, (List.hd RegSet.listItems(okColors)))
              end
             
           end
                 
     
    in
       build();
       makeWorkList(IntBinarySet.listItems(!initial));
       simplify(IntBinarySet.listItems(!simplifyWorkList));
       assignColors()
        
    end
            
end
