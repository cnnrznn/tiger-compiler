structure MakeGraph:
sig
    val instrs2graph: Assem.instr list -> Flow.flowgraph * Graph.node list
    val show: TextIO.outstream * Flow.flowgraph -> unit
end = struct

        structure A = Assem
  
        fun show (out, fg : Flow.flowgraph) =
           let
               val nodes = Graph.nodes (#control fg)
           in
              List.app
              (fn (n) =>
                  let val defList = case (Graph.Table.look( (#def fg), n)) of SOME l => l
                      val useList = case (Graph.Table.look( (#use fg), n)) of SOME l => l
                  in
                      TextIO.output(
                               out,
                               ( (Graph.nodename n) ^ ": \n" ^
                                "def: " ^ ( List.foldl (fn (t,s) => s ^ Frame.makeString t) ""  defList ) ^ "\n" ^
                                "use: " ^ ( List.foldl (fn (t,s) => s ^ Frame.makeString t) ""  useList ) ^ "\n" ^
                                "succ: " ^ (  List.foldl (fn (succ_n, s) => s ^ ","^Graph.nodename succ_n  ) "" (Graph.succ n)     ) ^ "\n" ^
                                "prev: " ^ (  List.foldl (fn (prev_n, s) => s ^ ","^Graph.nodename prev_n  ) "" (Graph.pred n)     ) ^ "\n"
                               )
                      )
                 end
              )
              nodes
           end 

        fun createNodes([], _) = []
          | createNodes(i::instrs, g: Graph.graph) =
                Graph.newNode(g) :: createNodes(instrs, g)

        fun populateFG([], [], fg) = fg
          | populateFG(i::instrs, n::nodes, fg: Flow.flowgraph) =
              let
                  val format0 = Assem.format(Frame.makeString)
              in
 
              ( TextIO.output(TextIO.stdOut,(Graph.nodename n)^":  "^(format0 i));
               case i
               of A.OPER{assem=_,
                         src=src,
                         dst=dst,
                         jump=_} =>
                        populateFG(instrs, nodes, {control= #control fg,
                                                   def=Graph.Table.enter(#def fg, n, dst),
                                                   use=Graph.Table.enter(#use fg, n, src),
                                                   ismove= Graph.Table.enter(#ismove fg, n, false)})
                | A.LABEL{assem=_, lab=lab} =>
                        populateFG(instrs, nodes, {control= #control fg,
                                                   def= Graph.Table.enter(#def fg, n, []),
                                                   use= Graph.Table.enter(#use fg, n, []),
                                                   ismove= Graph.Table.enter(#ismove fg, n, false)})
                | A.MOVE {assem=_, src=src, dst=dst} =>
                        populateFG(instrs, nodes, {control= #control fg,
                                                   def=Graph.Table.enter(#def fg, n, [dst]),
                                                   use=Graph.Table.enter(#use fg, n, [src]),
                                                   ismove= Graph.Table.enter(#ismove fg, n, true)}) 
                )
                end
 
        fun findNode(_, [], [], g) = (ErrorMsg.error 0 "catastrophic";
                                      Graph.newNode(g))
        fun findNode(l: Temp.label, i::instrs, n::nodes, g) =
                        case i
                         of A.LABEL{assem=_, lab=lab} =>
                                if l = lab
                                then n
                                else findNode(l, instrs, nodes, g)
                          | _ => findNode(l, instrs, nodes, g)

        fun makeEdges(_, [], _, _, _) = ()
          | makeEdges(n, l::labs, instrs, nodes, g) = (
                Graph.mk_edge{from=n, to=findNode(l, instrs, nodes, g)};
                makeEdges(n, labs, instrs, nodes, g)
                )

        fun createEdges([i],[n], iinstrs, nnodes, fg:Flow.flowgraph) =
              (case i
                    of A.OPER{assem=_, src=_, dst=_, jump=jump} =>
                         (case jump
                          of NONE => ()
                           | SOME labs => makeEdges(n, labs, iinstrs, nnodes, #control fg))
                    | _ => ()
                   )
              
          | createEdges(i::instrs, n::nodes, iinstrs, nnodes, fg: Flow.flowgraph) =
               let
                  val nextnode::restnodes = nodes                  
               in
                   (case i
                    of A.OPER{assem=_, src=_, dst=_, jump=jump} =>
                         (case jump
                          of NONE =>  Graph.mk_edge{from=n, to=nextnode}
                           | SOME labs => makeEdges(n, labs, iinstrs, nnodes, #control fg))
                    | _ => Graph.mk_edge{from=n, to=nextnode}
                   ;
               createEdges(instrs, nodes, iinstrs, nnodes, fg))
              end

    fun printNodes(nodes)=
       List.app (fn (n) => ErrorMsg.error 0 (Graph.nodename n)) nodes

    fun instrs2graph instrs =
        let val fg: Flow.flowgraph = {
                                control = Graph.newGraph(),
                                def = Graph.Table.empty,
                                use = Graph.Table.empty,
                                ismove = Graph.Table.empty}
            val nodes = createNodes(instrs, #control fg)
            val newFg = populateFG(instrs, nodes, fg)
        in createEdges(instrs, nodes, instrs, nodes, newFg);
           (*printNodes(nodes); *) 
           show(TextIO.stdOut, newFg);
           (newFg, nodes)
        end
end
