structure Liveness:
sig
    datatype igraph =
	IGRAPH of {graph: Graph.graph, 
		   tnode: Temp.temp -> Graph.node,
		   gtemp: Graph.node -> Temp.temp,
		   moves: (Graph.node * Graph.node) list }
    val interferenceGraph :
        Flow.flowgraph -> igraph * (Graph.node -> Temp.temp list)
    (*val show : outstream * igraph -> unit *)
end = struct
 
    (* interference graph datastructure *)
    datatype igraph = IGRAPH of {graph: Graph.graph, 
		   tnode: Temp.temp -> Graph.node,
		   gtemp: Graph.node -> Temp.temp,
		   moves: (Graph.node * Graph.node) list }

   
    type liveSet = unit Temp.Table.table * Temp.temp list
    type liveMap = liveSet Graph.Table.table

    (* function to initialize the live-in and live-out maps for each node *)
    fun initializeMaps(node :: nodes, liveInMap, liveOutMap ) =
          let
	      val newInMap = Graph.Table.enter (liveInMap, node, (Temp.Table.empty, []))
              val newOutMap = Graph.Table.enter (liveOutMap, node, (Temp.Table.empty, []))
          in 
	      initializeMaps(nodes, newInMap, newOutMap )
          end
        
        | initializeMaps([], liveInMap, liveOutMap ) = {liveInMap = liveInMap, liveOutMap = liveOutMap}
        

    (* function to perform liveness analysis given a control flow graph *)
    (* it has helper functions to solve the dataflow equations and make *)
    (* node wise updates to the live-in and live-out maps               *)

    fun calcLiveness ({ control, def, use, ismove }: Flow.flowgraph) =

        let 
           (* initialize the liveset and liveMap structures *)
	    val {liveInMap= inMapInit, liveOutMap= outMapInit} = initializeMaps(Graph.nodes control , Graph.Table.empty, Graph.Table.empty)
         
            (*function to update live-in Map for a particular a node *)
            (* this function returns the updated live-in map based on*)
            (* in[n] <-- use[n] U (out[n] - def [n]                  *)

            fun liveInMapUpdate(node,liveInMap, liveOutMap) =
                let
		    val (inTable, inList) = case Graph.Table.look (liveInMap, node) of
                                            SOME u => u
                    val (_, outList) = case Graph.Table.look (liveOutMap, node) of
                                              SOME u => u
                    val useList = case Graph.Table.look (use, node) of
                                   SOME u => u
          	    val defList =  case Graph.Table.look (def, node) of
                                   SOME d => d
                    val filterOut = List.filter
              			(fn t => 
                                 case ( List.find (fn d => t = d) defList)
                                 of SOME e => false
                                   | NONE =>  true) outList
                   val liveIn = useList @ filterOut 
                   (*doubt : is it a new temptable coz we are assigning live-in or is it adding just entering to table *)
                   val inTable_new = List.foldr (fn (k, t') => Temp.Table.enter (t', k, ())) inTable liveIn;
                   val inList_new = List.foldr (fn ((k,v), l) => k::l ) [] (IntBinaryMap.listItemsi(inTable_new));
                in
                   Graph.Table.enter(liveInMap, node, (inTable_new, inList_new))
                end 
            
            (*function to update live-out Map for a particular a node *)
            (* this returns the updated live-out map based on         *)
            (* out[n] <--- Union( in[s]) for all succ(n)              *)
            fun liveOutMapUpdate(node,liveInMap, liveOutMap)=
                let
                    val (outTable, outList) = case Graph.Table.look (liveOutMap, node) of
                                              SOME u => u
                    val succ_n = Graph.succ node
                    val outList_dups = List.foldr (fn (l,s) => 
							let val (_, inList) = case Graph.Table.look (liveInMap, node) of
                                                                              SOME m => m
                                                        in inList @ l
                                                        end ) [] succ_n
                    
                   val outTable_new = List.foldr (fn (k, t') => Temp.Table.enter (t', k, ())) outTable outList_dups;
                   val outList_new = List.foldr (fn ((k,v), l) => k::l ) [] (IntBinaryMap.listItemsi(outTable_new));
 
                in
                    Graph.Table.enter(liveOutMap, node, (outTable_new, outList_new))
                end 
            
            (* Function to update the live-in and live-out maps for all the nodes in one iteration*)
            fun mapUpdate(node::nodes, liveInMap, liveOutMap) = 
             (*code for updating the liveMaps for all nodes*)
              let
                 val liveInMap_new = liveInMapUpdate(node,liveInMap, liveOutMap);
                 val liveOutMap_new = liveOutMapUpdate(node,liveInMap_new, liveOutMap);
              in   
                 mapUpdate(nodes, liveInMap_new, liveOutMap_new )   
              end
              | mapUpdate([], liveInMap, liveOutMap) = (liveInMap , liveOutMap)
           
            (* helper function to determine equality of two maps *)
            fun isEqual(map1, map2) =
              let
                 fun extractLiveSetTab(map)=
                     List.foldr (fn ((tempTab, tempList), l) => tempTab :: l) [] (IntBinaryMap.listItems(map1))

                 val livesetTab1 =  extractLiveSetTab (map1);
                 val livesetTab2 =  extractLiveSetTab (map2);
              in
                  ListPair.allEq (fn (tab1, tab2) => 
                                     let val keyList1 = List.foldr (fn ((k,v), l) => k::l ) [] (IntBinaryMap.listItemsi(tab1))  
                                         val keyList2 = List.foldr (fn ((k,v), l) => k::l ) [] (IntBinaryMap.listItemsi(tab2)) 
                                     in keyList1 = keyList2 
                                     end) (livesetTab1, livesetTab2)
                  
              end

            
         
            (* Function for performing multiple iterations of mapUpdate for all nodes until the maps dont change*)
            fun iterUpdates(nodes, liveInMap, liveOutMap)=
                let
                    val (liveIn_new, liveOut_new) =   mapUpdate (nodes,liveInMap,liveOutMap )
                in
                   if ( isEqual (liveInMap,liveIn_new ) andalso isEqual (liveOutMap,liveOut_new )) then

                	(liveIn_new, liveOut_new)
            	   else
                	iterUpdates (nodes, liveIn_new, liveOut_new )
		    
                end        
             
        in
           iterUpdates(Graph.nodes control,inMapInit,outMapInit )
                  
        end

    (* function which performs liveness analysis and  builds the interference graph for all the temps *)
    fun interferenceGraph (Flow.FGRAPH { control, def, use, ismove }) =
        let

           (* perform liveness analysis and get live-in and live-out maps *)
           val (liveInMap, liveOutMap) = calcLiveness( Flow.FGRAPH { control=control, def=def, use=use, ismove=ismove })
           (* initialize the graph *)
           val graph = Graph.newGraph ()
           (* a table to keep track of the temp-> node mapping *)
           val nodeTracker = ref Temp.Table.empty

           fun tempToNode (temp) = 
               case Temp.Table.look(!nodeTracker, temp) of
               SOME n => n
               | NONE => let val n = Graph.newNode (graph)
                         in nodeTracker := Temp.Table.enter(!nodeTracker, temp, n);
                            n
                         end
           
                 
           fun nodeToTemp (node) = 
             case List.find (fn (k,v) => Graph.eq node v )(IntBinaryMap.listItemsi(!nodeTracker)) of
                SOME (temp, _) => temp
                | NONE         => (ErrorMsg.error 0 "Error in nodeToTemp" ; Temp.newtemp()) 
          
           (* Show graph needs to be implemented *)

           (* function to construct the interference graph   *)
           fun constructGraph(nodes) =
             let   
                val moves = ref []              
                fun addEdges(node)=
                    let
                       (*get the defs *)
                       val defList = case Graph.Table.look (def, node) of SOME dl => dl
                       val useList = case Graph.Table.look (use, node) of SOME ul => ul
                       (* get live temps *)
                       val (liveTable, liveList) = Graph.Table.look (liveOutMap, node)                         
                    in
                        (* make edges between def and live temps*)
                        (* before making edges check if the node is already present in the igraph for that temp*)
                        (* if not make a node *) 
                      List.app ( ( fn d =>  
                                      List.app ((fn l =>
                                                    if d = l then ()
                                                    else Graph.mk_edge {from= tempToNode d , to =  tempToNode l }) ,
                                                liveList), 
                                 defList));
                      (* adding tuples to moves datastructure *)
                      case Graph.Table.look(ismove, node) of
                         SOME b => (if b then
                                      moves := (List.hd useList, List.hd defList ) :: !moves
                                   else () )
                         |NONE => ErrorMsg.error 0 "Catastrophic error in addEgdes "
                    end
             in
                 List.app addEdges nodes;
                 IGRAPH {graph = graph, tnode = tempToNode, gtemp= nodeToTemp, moves = !moves }
                 
             end
           
        in
           constructGraph(Graph.nodes control)
        end 
  
    (* caclulate live in and live out *)
    (* fill up the liveSet and livemap structures for each node *)
    (*consytuct interference Map*)
	
end
