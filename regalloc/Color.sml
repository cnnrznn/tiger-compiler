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

        fun getAdjNodes node = 
           NodeSet.listItems(NodeSet.addList(NodeSet.empty, Graph.adj node))  
            
        fun degreeof (node) =
            List.length (getAdjNodes(node))   

        val degree = List.foldr (fn (n, t)  => ref ( Graph.Table.enter (!t, n, degreeof n )) ) (ref Graph.Table.empty) (Graph.nodes graph)
        val color : allocation ref = ref Temp.Table.empty
     
        fun showWorklists() =
            let 
               val initial_list = List.foldr (fn (k,l) => l ^ "("^ Frame.makeString (gTemp k)  ^")") "" (NodeSet.listItems(!initial))
               val simp_list = List.foldr (fn (k,l) => l ^ "("^ Frame.makeString( gTemp k) ^ ")") "" (NodeSet.listItems(!simplifyWorkList))
               val spill_list = List.foldr (fn (k,l) => l ^ "("^ Frame.makeString (gTemp k) ^")") "" (NodeSet.listItems(!spillWorkList))
               val workmove_list = List.foldr (fn ((k,v),l) => l ^ "(  ("^ Frame.makeString (gTemp k)^" , "^ Frame.makeString (gTemp v) ^")") "" (MoveSet.listItems(!moveWorkList))
               val active_list = List.foldr (fn ((k,v),l) => l ^ "(  ("^ Frame.makeString (gTemp k)^" , "^ Frame.makeString (gTemp v) ^")") "" (MoveSet.listItems(!activeMoves))
               
               val coalesced_list = List.foldr (fn (k,l) => l ^ "("^ Frame.makeString (gTemp k) ^")") "" (NodeSet.listItems(!coalescedNodes))
               val freeze_list = List.foldr (fn (k,l) => l ^ "("^ Frame.makeString (gTemp k) ^")") "" (NodeSet.listItems(!freezeWorkList))
               
             in
                TextIO.output ( TextIO.stdOut , "\n\n******** WorkLists ******** ");
                TextIO.output ( TextIO.stdOut , "\n\n initial Worklist : "^ initial_list ^ "\n");
                TextIO.output ( TextIO.stdOut , "\n\n simplify Worklist : "^ simp_list ^ "\n");
                TextIO.output ( TextIO.stdOut , "\n\n spill Worklist : "^ spill_list ^ "\n");
                TextIO.output ( TextIO.stdOut , "\n\n move Worklist : "^ workmove_list ^ "\n");
                TextIO.output ( TextIO.stdOut , "\n\n active move Worklist : "^ active_list ^ "\n");
                TextIO.output ( TextIO.stdOut , "\n\n coalesced Worklist : "^ coalesced_list ^ "\n");
                TextIO.output ( TextIO.stdOut , "\n\n freeze Worklist : "^ freeze_list ^ "\n")
             end

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
                    moves;

                    makeMoveWorkList(moves)

                )

        and makeMoveWorkList([]) = ()
          | makeMoveWorkList(m::moves) = (
                moveWorkList := MoveSet.add(!moveWorkList, m);
                makeMoveWorkList(moves)
                )

        fun NodeMoves(n) =
                let val mln = case Graph.Table.look(!moveList, n)
                               of SOME set => set
                                | NONE => (ErrorMsg.error 0 "fatal in <NodeMoves>";
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

        fun MoveRelated(n) = not( MoveSet.isEmpty(NodeMoves(n)))


        fun makeWorkList(node::nodes) = 
            let val k = List.length registers
            in 
             ( initial := NodeSet.delete(!initial, node); 
               case  Graph.Table.look (!degree, node) of
                   SOME d => if d >= k then
                                 spillWorkList := NodeSet.add(!spillWorkList, node)
                         
                             else if MoveRelated(node) then
                                freezeWorkList := NodeSet.add(!freezeWorkList, node)
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
          | EnableMoves(n::nodes) =
                let fun forEachMove([]) = ()
                      | forEachMove(m::moves) =
                                ( (*TextIO.output ( TextIO.stdOut , "\n\n inside EnableMoves "); *)
                                  if MoveSet.member(!activeMoves, m) then
                                        (activeMoves := MoveSet.delete(!activeMoves, m);
                                        moveWorkList := MoveSet.add(!moveWorkList, m))
                                  else ();
                                 forEachMove(moves))
                in  
                     TextIO.output ( TextIO.stdOut , "\n\n inside EnableMoves for node : "^ Frame.makeString (gTemp n));
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
                in 
                   TextIO.output ( TextIO.stdOut , "\n\n inside Coalesce for move : ("^ Frame.makeString(gTemp x')^" , " ^ Frame.makeString(gTemp y') ^")" );
                   showWorklists();
                   moveWorkList := MoveSet.delete(!moveWorkList, m);
                   showWorklists();
                   
                   if Graph.eq(u, v) then
                        (TextIO.output ( TextIO.stdOut , "\n\n inside Coalesce Graph.eq(u, v)");
                         coalescedMoves := MoveSet.add(!coalescedMoves, m);
                        AddWorkList(u)
                         )
                   else if NodeSet.member(!precoloredNodes, v) orelse adjSet(u, v) then
                        (TextIO.output ( TextIO.stdOut , "\n\n inside Coalesce orelse adjSet(u, v");
                         constrainedMoves := MoveSet.add(!constrainedMoves, m);
                        AddWorkList(u);
                        AddWorkList(v)
                        )
                   else if ((NodeSet.member(!precoloredNodes, u) andalso
                                allOK(NodeSet.listItems(Adjacent(v)), u)) orelse
                                (not(NodeSet.member(!precoloredNodes, u)) andalso
                                Conservative(NodeSet.listItems(NodeSet.union(Adjacent(u), Adjacent(v)))))) then
                        (TextIO.output ( TextIO.stdOut , "\n\n inside Coalesce last condition");
                         coalescedMoves := MoveSet.add(!coalescedMoves, m);
                         Combine(u, v);
                         AddWorkList(u)
                        )
                   else
                        (TextIO.output ( TextIO.stdOut , "\n\n inside Coalesce  else");
                         activeMoves := MoveSet.add(!activeMoves, m)
                        )
                   
                end

        and AddWorkList(u) =
                let val deg = case Graph.Table.look(!degree, u)
                                of SOME d => d
                                 | NONE => (ErrorMsg.error 0 "catastrophic in <AddWorkList>";
                                            0)
                in
                        TextIO.output ( TextIO.stdOut , "\n\n inside AddworkList");
                        if not(NodeSet.member(!precoloredNodes, u)) andalso not(MoveRelated(u)) andalso
                                        deg < K
                                         then
                                ( 
                                 if NodeSet.member(!freezeWorkList, u) then freezeWorkList := NodeSet.delete(!freezeWorkList, u) else (); (* this was the source of the uncaught exception*)
                                 (*TextIO.output ( TextIO.stdOut , "\n\n inside AddworkList if condition"); *)
                                 simplifyWorkList := NodeSet.add(!simplifyWorkList, u))
                        else ()
                end

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
                in 
                   TextIO.output (TextIO.stdOut , "\n\n inside Combine. node: "^ Frame.makeString(gTemp v));
                   showWorklists();
                   if NodeSet.member(!freezeWorkList, v) then
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

                   EnableMoves([v]);

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
                if not (NodeSet.member(!precoloredNodes, node)) then
                   (TextIO.output ( TextIO.stdOut , "\n\n inside DecrementDegree. Degree "^ Frame.makeString(gTemp node));
                    degree := Graph.Table.enter(!degree, node, (deg-1)) ;
                    if deg = k then
                       (EnableMoves(node :: NodeSet.listItems(Adjacent(node)));
                        showWorklists() ;
                        spillWorkList := NodeSet.delete(!spillWorkList, node);
               
                        if MoveRelated(node) then
                            freezeWorkList := NodeSet.add(!freezeWorkList, node)
                        else
                            simplifyWorkList := NodeSet.add(!simplifyWorkList, node) )
                    else ())
                else ()
            end
           
        
        fun simplify() =
           let
              
               val node = List.hd ( NodeSet.listItems(!simplifyWorkList))
           in
                    (
                     simplifyWorkList := NodeSet.delete(!simplifyWorkList, node);
                     
                     selectStack := node :: !selectStack;

                     List.app (fn n => DecrementDegree n) (NodeSet.listItems(Adjacent(node))) )
                    (* TextIO.output ( TextIO.stdOut , "\n\n inside simplify at end ") ) *)


           end 
                       
           
       fun assignColors(node) =
           let 
              val adjlist = getAdjNodes node
              val okColors = RegSet.addList( RegSet.empty , registers)
              val u = NodeSet.union(!coloredNodes, !precoloredNodes)
           in
             (print("\ninside Assign Colors\n");
              let
                  val remColors = List.foldr (fn (a,c) => 
                                                let val w = GetAlias(a)
                                                in (print("\ninside Assign Colors\n");
                                                         if NodeSet.member(u, w) then
                                                             case Temp.Table.look(!color, (gTemp w)) of
                                                                 SOME colr => if RegSet.member(c, colr) then RegSet.delete(c, colr)
                                                                              else c  
                                                                 |NONE => (ErrorMsg.error 0 "Error in assignColors" ; c)
                                                              
                                                          else c )
                                                end) okColors adjlist
                                                         
              in 
                 ( print("\ninside Assign Colors before remcolors\n");
                  if RegSet.isEmpty( remColors) then
                      spilledNodes := NodeSet.add(!spilledNodes, node)
                  else
                      coloredNodes := NodeSet.add(!coloredNodes, node) ;
                      color := Temp.Table.enter(!color, (gTemp node), List.hd (RegSet.listItems(remColors)))
                      (*printAllocation()*))
              end)
             
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
                simplifyWorkList := NodeSet.add(!simplifyWorkList, spillNode);
                (* freeze MOves *)
                TextIO.output ( TextIO.stdOut , "\n\n entereted FreezeMoves");
                FreezeMoves(spillNode)
                   
           end

            
       fun repeatFunc() =
          if not (NodeSet.isEmpty(!simplifyWorkList)) then 
             (TextIO.output ( TextIO.stdOut , "\n\n entereted simplify"); simplify(); repeatFunc())
          else if not (MoveSet.isEmpty(!moveWorkList)) then
                (TextIO.output ( TextIO.stdOut , "\n\n entereted Coalesce") ; Coalesce(); repeatFunc())
          else if not (NodeSet.isEmpty(!freezeWorkList)) then
                (TextIO.output ( TextIO.stdOut , "\n\n entereted Freeze") ; Freeze(); repeatFunc())
          else if not (NodeSet.isEmpty(!spillWorkList) ) then 
               (TextIO.output ( TextIO.stdOut , "\n\n entereted selectSpill"); selectSpill() ; repeatFunc())
          else ()
    in
       build();
       TextIO.output ( TextIO.stdOut , "\n\n number of nodes in initial worklist :"^ Int.toString( NodeSet.numItems(!initial)));
       
       makeWorkList(NodeSet.listItems(!initial));
  
       TextIO.output ( TextIO.stdOut , "\n\n number of nodes in simplify worklist : "^Int.toString( NodeSet.numItems(!simplifyWorkList))); 
       repeatFunc();


       print("\nrepeatFunc\n");
      
       List.app (fn (n) => assignColors(n)) (!selectStack);
       print("repeatFunc\n");
       
       List.app (fn (n) => let val m = GetAlias(n)
                           in color := Temp.Table.enter(!color, gTemp n, 
                                                case Temp.Table.look(!color, gTemp m)
                                                 of SOME c => c
                                                  | NONE => ("woops"))
                           end
                ) (NodeSet.listItems(!coalescedNodes));

       (*ErrorMsg.error 0 ("number of spilled nodes " ^ Int.toString( NodeSet.numItems(!spilledNodes))); *)
       ( !color ,  List.map (fn (n) => gTemp n) (NodeSet.listItems(!spilledNodes)) )
    end
            
end
