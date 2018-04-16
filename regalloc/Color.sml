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
   
    structure NodeSet = ListSetFn(
       type ord_key = Graph.node
       fun compare ((_,a),(_,b)) = 
                                   if a=b then
                                       EQUAL
                                   else if a < b then
                                       LESS
                                   else  GREATER )
    
    structure NodeTupleSet = ListSetFn(
       type ord_key = Graph.node * Graph.node
       fun compare (n1, n2) = 
                                   if a=b then
                                       EQUAL
                                   else if a < b then
                                       LESS
                                   else  GREATER )

    structure Frame = MipsFrame
    type allocation = Frame.register Temp.Table.table
   
   
    fun color (Liveness.IGRAPH{graph, tnode, gTemp, moves} , initPre , spillCost, registers ) =
    let
        (* all the workslists *)
        val simplifyWorkList = ref NodeSet.empty
        val spillWorkList = ref NodeSet.empty
        val moveWorkList = ref NodeSet.empty 
        val moveList = ref Graph.Table.empty
        val coloredNodes = ref NodeSet.empty
        val precoloredNodes = ref NodeSet.empty
        val initial = ref NodeSet.empty
        val spilledNodes = ref NodeSet.empty
        val selectStack : Graph.node list ref = ref []

        val degree = List.foldr (fn (n, t)  => ref ( Graph.Table.enter (!t, n, degreeof n )) ) (ref Graph.Table.empty) (Graph.nodes graph)
        val color = ref Graph.Table.empty
     
        fun degreeof (node) =
            List.length (Graph.adj(node))     
  
        fun build() =
            ( List.app  ( fn (t,r)  =>  let 
                                           val n : Graph.node  = tnode t
                                        in  
                                           ( precoloredNodes := NodeSet.add(!precoloredNodes, n) ;
                                            color := Graph.Table.enter(!color, n,r) )
                                        end )  ( IntBinaryMap.listItemsi(initPre) ) ; 

       
       
           (* initialize initial structure*)
           List.app ( fn (node) => let 
                                      val t = gTemp node
                                   in
                                      case Temp.Table.look(initPre, t) of
                                          SOME reg => coloredNodes :=  NodeSet.add(!coloredNodes, node) 
                                          | NONE  =>  initial := NodeSet.add(!initial, node)
                                   end )  (Graph.nodes graph) )
       
           (* make the moveList Table *)
           (* List.app (fn ( (n1,n2), t) => (t := Temp.Table.enter (!t, n1, n2); t := Temp.Table.enter (!t, n2, n1) )) moveList moves ) *)



        fun makeWorkList(node::nodes) = 
            let val k = List.length registers
            in 
              case  Graph.Table.look (!degree, node) of
                   SOME d => if d >= k then
                                 spillWorkList := NodeSet.add(!spillWorkList, node)
                             else
                                 simplifyWorkList := NodeSet.add(!simplifyWorkList, node)
                  |NONE =>  (ErrorMsg.error 0 "Error in makeWorkList" ; INT 0)
              
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
                  (spillWorkList := NodeSet.delete(!spillWorkList, node);
                   simplifyWorkList := NodeSet.add(!simplifyWorkList, node) )
              else ()
            end
           
        
        fun simplify(node :: nodes) =
           let
               val adjnodes = Graph.adj(node)
           in
              (simplifyWorkList := NodeSet.delete(!simplifyWorkList, node);
               selectStack := node :: !selectStack;
               List.app (fn n => decrementDegree n) adjnodes ;
               simplify(nodes) )
           end
            
            | simplify ([]) = ()
            
           
       fun assignColors(node) =
           let 
              val adjlist = Graph.adj node
              val okColors = RegSet.addList( RegSet.empty , registers)
              val u = NodeSet.union(!coloredNodes, !precoloredNodes)
           in
              let
                  val remColors = List.foldr (fn (a,c) => if NodeSet.member(u, a) then
                                                             case Graph.Table.look(!color, a) of
                                                                 SOME colr => RegSet.delete(c, colr)
                                                                |NONE => (ErrorMsg.error 0 "Error in assignColors" ; c)
                                                              
                                                          else c ) okColors adjlist
                                                          
              in 
                  if RegSet.isEmpty( remColors) then
                      spilledNodes := NodeSet.add(!spilledNodes, node)
                  else
                      coloredNodes := NodeSet.add(!coloredNodes, node) ;
                      color := Graph.Table.enter(!color, node, List.hd (RegSet.listItems(okColors)))
              end
             
           end
                 
     
    in
       build();
       makeWorkList(NodeSet.listItems(!initial));
       simplify(NodeSet.listItems(!simplifyWorkList));
       List.app (fn (n) => assignColors(n)) (Graph.nodes graph)

       
        
    end
            
end
