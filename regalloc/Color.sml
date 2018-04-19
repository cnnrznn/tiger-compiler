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
   
        structure MoveSet = ListSetFn(
                type ord_key = Graph.node * Graph.node
                fun compare (((_, a), (_, b)), ((_, c), (_, d))) = (
                        if a = c then
                                if b = d then
                                        EQUAL
                                else if b < d then
                                        LESS
                                else    GREATER
                        else if a < c then
                                LESS
                        else    GREATER
                )
        )

    structure Frame = MipsFrame
    type allocation = Frame.register Temp.Table.table
   
   
    fun color ({ interference = Liveness.IGRAPH{graph = graph, tnode =tnode, gtemp= gTemp, moves=  moves} , initial = initPre , spillCost = spillCost, registers = registers} ) =
    let
        val K = 32

        (* all the workslists *)
        val simplifyWorkList = ref NodeSet.empty
        val spillWorkList = ref NodeSet.empty
        val moveWorkList = ref MoveSet.empty
        val moveList: MoveSet.set Graph.Table.table ref = ref Graph.Table.empty
        val coalescedNodes = ref NodeSet.empty
        val alias = ref Graph.Table.empty
        val freezeWorkList = ref NodeSet.empty
        val coloredNodes = ref NodeSet.empty
        val precoloredNodes = ref NodeSet.empty
        val initial = ref NodeSet.empty
        val spilledNodes = ref NodeSet.empty
        val selectStack : Graph.node list ref = ref []

        val activeMoves = ref MoveSet.empty
        val frozenMoves = ref MoveSet.empty
        val coalescedMoves = ref MoveSet.empty
        val constrainedMoves = ref MoveSet.empty

        fun adjSet(u, v) =
                let val adj = Graph.adj u
                    fun findNode(t) = Graph.eq(t, v)
                in List.exists findNode adj
                end

        fun degreeof (node) =
            List.length (Graph.adj(node))   

        val degree = List.foldr (fn (n, t)  => ref ( Graph.Table.enter (!t, n, degreeof n )) ) (ref Graph.Table.empty) (Graph.nodes graph)
        val color : allocation ref = ref Temp.Table.empty
     
        fun printAllocation() =
           let val alloc_list = List.foldr (fn ((k,v),l) => l ^ "("^ Temp.makestring k ^" , " ^ v ^")\n\n") "" (IntBinaryMap.listItemsi(!color))
             in ErrorMsg.error 0  alloc_list
             end 
       
  
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
                                   end )  (Graph.nodes graph) ;
       
           (* make the moveList Table *)
           List.app (fn (n1,n2) => (let val s1 = case Graph.Table.look(!moveList, n1)
                                                  of SOME set => set
                                                   | NONE => MoveSet.empty
                                        val s2 = case Graph.Table.look(!moveList, n2)
                                                  of SOME set => set
                                                   | NONE =>MoveSet.empty
                                        val ns1 = MoveSet.add(s1, (n1, n2))
                                        val ns2 = MoveSet.add(s2, (n1, n2))
                                    in moveList := Graph.Table.enter(!moveList, n1, ns1);
                                       moveList := Graph.Table.enter(!moveList, n2, ns2)
                                    end
                                )
                    )
                    moves
                )

        fun makeMoveWorkList([]) = ()
          | makeMoveWorkList(m::moves) = (
                moveWorkList := MoveSet.add(!moveWorkList, m);
                makeMoveWorkList(moves)
                )

        fun NodeMoves(n) =
                let val mln = case Graph.Table.look(!moveList, n)
                               of SOME set => set
                                | NONE => (ErrorMsg.error 0 "fatal in <MoveRelated()>";
                                                MoveSet.empty)
                in
                   MoveSet.intersection(
                           mln,
                           MoveSet.union(
                                   !activeMoves,
                                   !moveWorkList
                           )
                   )
                end

        fun MoveRelated(n) = MoveSet.isEmpty(NodeMoves(n))


        fun makeWorkList(node::nodes) = 
            let val k = List.length registers
            in 
             ( case  Graph.Table.look (!degree, node) of
                   SOME d => if d >= k then
                                 spillWorkList := NodeSet.add(!spillWorkList, node)
                         
                             else
                                ( simplifyWorkList := NodeSet.add(!simplifyWorkList, node);
                                 ())
                  |NONE =>  (ErrorMsg.error 0 "Error in makeWorkList" ; ()) ;
                 makeWorkList(nodes))
              
            end
           | makeWorkList([]) = ()

        fun Adjacent(n) =
                (* adjList[n].difference(selectStack U coalescedNodes) *)
                let val adj = NodeSet.addList(NodeSet.empty,
                                                Graph.adj n)
                    val set = NodeSet.union(NodeSet.addList(NodeSet.empty, !selectStack),
                                            !coalescedNodes)
                in  NodeSet.difference(adj, set)
                end

        fun EnableMoves([]) = ()
        fun EnableMoves(n::nodes) =
                let fun forEachMove([]) = ()
                    fun forEachMove(m::moves) =
                        if MoveSet.member(!activeMoves, m) then
                                (activeMoves := MoveSet.delete(!activeMoves, m);
                                moveWorkList := MoveSet.add(!moveWorkList, m))
                        else ()
                in
                    forEachMove(MoveSet.listItems(NodeMoves(n)));
                    EnableMoves(nodes)
                end

        fun Coalesce() =
                let val (x',y') = List.hd(MoveSet.listItems(!moveWorkList))
                    val m = (x', y')
                    val x = GetAlias(x')
                    val y = GetAlias(y')
                    val (u, v) = if NodeSet.member(!precoloredNodes, y) then
                                        (y, x)
                                 else   (x, y)
                in moveWorkList := MoveSet.delete(!moveWorkList, m);
                   if Graph.eq(u, v) then
                        (coalescedMoves := MoveSet.add(!coalescedMoves, m);
                        AddWorkList(u))
                   else if NodeSet.member(!precoloredNodes, v) orelse adjSet(u, v) then
                        (constrainedMoves := MoveSet.add(!constrainedMoves, m);
                        AddWorkList(u);
                        AddWorkList(v))
                   else if ((NodeSet.member(!precoloredNodes, u) andalso
                                allOK(NodeSet.listItems(Adjacent(v)), u)) orelse
                                (not(NodeSet.member(!precoloredNodes, u)) andalso
                                Conservative(NodeSet.listItems(NodeSet.union(Adjacent(u), Adjacent(v)))))) then
                        (coalescedMoves := MoveSet.add(!coalescedMoves, m);
                        Combine(u, v);
                        AddWorkList(u))
                   else
                        activeMoves := MoveSet.add(!activeMoves, m)
                end

        and AddWorkList(u) =
                if not(NodeSet.member(!precoloredNodes, u)) andalso not(MoveRelated(u))
                                 then
                        (freezeWorkList := NodeSet.delete(!freezeWorkList, u);
                        simplifyWorkList := NodeSet.add(!simplifyWorkList, u))
                else ()

        and allOK(nodes, u) =
                List.all (fn t => OK(t, u)) 
                         nodes

        and OK (t: Graph.node, r: Graph.node) =
                let val deg = case Graph.Table.look(!degree, t)
                                of SOME d => d
                                 | NONE => (ErrorMsg.error 0 "catastrophic in <OK()>";
                                            0)
                in ((deg < K) orelse NodeSet.member(!precoloredNodes, t) orelse
                                adjSet(t, r))
                end

        and Conservative(nodes) =
                let
                    fun highDeg([], k) = k
                      | highDeg(n::nodes, k) =
                        let val deg = case Graph.Table.look(!degree, n)
                                        of SOME d => d
                                         | NONE => (ErrorMsg.error 0 "catastrophic in <Conservative()>";
                                                    0)
                        in if deg >= K then
                                highDeg(nodes, k + 1)
                           else highDeg(nodes, k)
                        end
                    val k = highDeg(nodes, 0)
                in k < K
                end

        and GetAlias(n) =
                if NodeSet.member(!coalescedNodes, n) then
                        let val m = case Graph.Table.look(!alias, n)
                                     of SOME u => u
                                      | NONE => (ErrorMsg.error 0 "catastrophic in <GetAlias()>";
                                                 n)
                        in GetAlias(m)
                        end
                else n

        and Combine(u, v) =
                let val ml = case Graph.Table.look(!moveList, v)
                              of SOME l => l
                               | NONE => (ErrorMsg.error 0 "catastrophic in <Combine>";
                                      MoveSet.empty)
                    fun combineEdges(t) = (
                        Graph.mk_edge{from=t, to=u};
                        DecrementDegree(t)
                        )
                    val deg = case Graph.Table.look(!degree, u)
                                of SOME d => d
                                 | NONE => (ErrorMsg.error 0 "catastrophic in <OK()>";
                                            0)
                in if NodeSet.member(!freezeWorkList, v) then
                           freezeWorkList := NodeSet.delete(!freezeWorkList, v)
                   else
                        spillWorkList := NodeSet.delete(!spillWorkList, v);

                   coalescedNodes := NodeSet.add(!coalescedNodes, v);
                   alias := Graph.Table.enter(!alias, v, u);

                   let val set1 = case Graph.Table.look(!moveList, u)
                                  of SOME s => s
                                   | NONE => (ErrorMsg.error 0 "catastrophic in <Combine>";
                                              MoveSet.empty)
                       val set2 = case Graph.Table.look(!moveList, v)
                                  of SOME s => s
                                   | NONE => (ErrorMsg.error 0 "catastrophic in <Combine>";
                                              MoveSet.empty)
                   in moveList := Graph.Table.enter(!moveList, u, MoveSet.union(set1, set2))
                   end;

                   List.app combineEdges (NodeSet.listItems(Adjacent(v)));
                   if deg >= K andalso (NodeSet.member(!freezeWorkList, u)) then
                        (freezeWorkList := NodeSet.delete(!freezeWorkList, u);
                        spillWorkList := NodeSet.add(!spillWorkList, u))
                   else ()
                end

        and Freeze() =
                let val u = List.hd(NodeSet.listItems(!freezeWorkList))
                in freezeWorkList := NodeSet.delete(!freezeWorkList, u);
                   simplifyWorkList := NodeSet.add(!simplifyWorkList, u);
                   FreezeMoves(u)
                end

        and FreezeMoves(u : Graph.node) =
                let fun forAllMoves(m) =
                        let val (x, y) = m
                            val v = if Graph.eq(GetAlias(u), GetAlias(y))then
                                         GetAlias(x)
                                    else GetAlias(y)
                            val deg = case Graph.Table.look (!degree, v) of
                               SOME d => d
                               |NONE  => (ErrorMsg.error 0 "Error in freezeMoves" ;  0)
                        in activeMoves := MoveSet.delete(!activeMoves, m);
                           frozenMoves := MoveSet.add(!frozenMoves, m);
                           if MoveSet.isEmpty(NodeMoves(v)) andalso deg < K then
                                (freezeWorkList := NodeSet.delete(!freezeWorkList, v);
                                simplifyWorkList := NodeSet.add(!simplifyWorkList, v))
                           else ()
                        end
                in List.app forAllMoves (MoveSet.listItems(NodeMoves(u)))
                end

        and DecrementDegree(node) =
            let 
                val deg = case Graph.Table.look (!degree, node) of
                        SOME d => d
                        |NONE  => (ErrorMsg.error 0 "Error in Decrementdegree" ;  0)
                val k = List.length registers
                 
            in
              degree := Graph.Table.enter(!degree, node, (deg-1)) ;
              if deg = k then
                  (EnableMoves(node :: NodeSet.listItems(Adjacent(node)));
                   spillWorkList := NodeSet.delete(!spillWorkList, node);
                   if MoveRelated(node) then
                         freezeWorkList := NodeSet.add(!freezeWorkList, node)
                   else
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

                     (*let val adjList =  List.foldr (fn (t,l) => l ^ (Temp.makestring (gTemp t)) ^ " ," ) "" (adjnodes)
                      in ErrorMsg.error 0 ("adj nodes of "^(Temp.makestring( (gTemp node)))^" : "^ (adjList))
                     end;*)
                     List.app (fn n => DecrementDegree n) adjnodes )

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
                      color := Temp.Table.enter(!color, (gTemp node), List.hd (RegSet.listItems(remColors)))
                      (*printAllocation()*)
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
       (*ErrorMsg.error 0 (Int.toString( NodeSet.numItems(!initial)));*)
       makeWorkList(NodeSet.listItems(!initial));
       (*ErrorMsg.error 0 (Int.toString( NodeSet.numItems(!simplifyWorkList))); *) 
       repeatFunc();
      
       List.app (fn (n) => assignColors(n)) (!selectStack);
       (*ErrorMsg.error 0 ("number of spilled nodes " ^ Int.toString( NodeSet.numItems(!spilledNodes))); *)
       ( !color ,  List.map (fn (n) => gTemp n) (NodeSet.listItems(!spilledNodes)) )
    end
            
end
