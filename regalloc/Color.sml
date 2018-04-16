signature COLOR =
sig 
    structure Frame: FRAME
    type allocation
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
   

    structure Frame = MipsFrame
    type allocation = Frame.register Temp.Table.table
   
   
    fun color ({ interference = Liveness.IGRAPH{graph = graph, tnode =tnode, gtemp= gTemp, moves=  moves} , initial = initPre , spillCost = spillCost, registers = registers} ) =
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

        fun degreeof (node) =
            List.length (Graph.adj(node))   

        val degree = List.foldr (fn (n, t)  => ref ( Graph.Table.enter (!t, n, degreeof n )) ) (ref Graph.Table.empty) (Graph.nodes graph)
        val color : allocation ref = ref Temp.Table.empty
     
          
  
        fun build() =
            ( List.app  ( fn (t,r)  =>  let 
                                           val n : Graph.node  = tnode t
                                        in  
                                           ( precoloredNodes := NodeSet.add(!precoloredNodes, n) ;
                                            color := Temp.Table.enter(!color, t,r) )
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
                  |NONE =>  (ErrorMsg.error 0 "Error in makeWorkList" ; ())
              
            end
           | makeWorkList([]) = ()

        fun decrementDegree(node) =
            let 
                val deg = case Graph.Table.look (!degree, node) of
                        SOME d => d
                        |NONE  => (ErrorMsg.error 0 "Error in decrementdegree" ;  0)
                val k = List.length registers
                 
            in
              degree := Graph.Table.enter(!degree, node, (deg-1)) ;
              if deg = k then
                  (spillWorkList := NodeSet.delete(!spillWorkList, node);
                   simplifyWorkList := NodeSet.add(!simplifyWorkList, node) )
              else ()
            end
           
        
        fun simplify() =
           let
              
               val node = List.hd ( NodeSet.listItems(!simplifyWorkList))
               val adjnodes = Graph.adj(node)
           in
                    (simplifyWorkList := NodeSet.delete(!simplifyWorkList, node);
                     selectStack := node :: !selectStack;
                     List.app (fn n => decrementDegree n) adjnodes )
           end 
                       
           
       fun assignColors(node) =
           let 
              val adjlist = Graph.adj node
              val okColors = RegSet.addList( RegSet.empty , registers)
              val u = NodeSet.union(!coloredNodes, !precoloredNodes)
           in
              let
                  val remColors = List.foldr (fn (a,c) => if NodeSet.member(u, a) then
                                                             case Temp.Table.look(!color, (gTemp a)) of
                                                                 SOME colr => RegSet.delete(c, colr)
                                                                |NONE => (ErrorMsg.error 0 "Error in assignColors" ; c)
                                                              
                                                          else c ) okColors adjlist
                                                          
              in 
                  if RegSet.isEmpty( remColors) then
                      spilledNodes := NodeSet.add(!spilledNodes, node)
                  else
                      coloredNodes := NodeSet.add(!coloredNodes, node) ;
                      color := Temp.Table.enter(!color, (gTemp node), List.hd (RegSet.listItems(okColors)))
              end
             
           end
        
       fun selectSpill() =
           let
               fun chooseSpill(minNode, node::nodes) = 
                 ( let val cost1 = spillCost minNode
                       val cost2 = spillCost node
                   in
                       if cost1 < cost2 then
                           chooseSpill(minNode, nodes)
                       else
                           chooseSpill(node, nodes) 
                       end)
                     
                  | chooseSpill(minNode, []) = minNode
                      
                val spillNode = chooseSpill(List.hd (NodeSet.listItems(!spillWorkList)), NodeSet.listItems(!spillWorkList))
            in
                spillWorkList := NodeSet.delete(!spillWorkList, spillNode);
                simplifyWorkList := NodeSet.add(!simplifyWorkList, spillNode)  
                (* freeze MOves *)                    
                   
           end

            
       fun repeatFunc() =
          if not (NodeSet.isEmpty(!simplifyWorkList)) then 
             (simplify(); repeatFunc())
          else if not (NodeSet.isEmpty(!spillWorkList) ) then 
              (selectSpill() ; repeatFunc())
          else ()
    in
       build();
       makeWorkList(NodeSet.listItems(!initial));
       repeatFunc();
       List.app (fn (n) => assignColors(n)) (Graph.nodes graph);
       
       ( !color ,  List.map (fn (n) => gTemp n) (NodeSet.listItems(!spilledNodes)) )
    end
            
end
