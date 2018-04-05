structure MakeGraph:
sig
    val instrs2graph: Assem.instr list -> Flow.flowgraph * Graph.node list
end = struct

        structure A = Assem

        fun createNodes([], _) = []
          | createNodes(i::instrs, g: Graph.graph) =
                Graph.newNode(g) :: createNodes(instrs, g)

        fun populateFG([], [], fg) = fg
          | populateFG(i::instrs, n::nodes, fg: Flow.flowgraph) =
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
                                                   def= #def fg,
                                                   use= #use fg,
                                                   ismove= Graph.Table.enter(#ismove fg, n, false)})
                | A.MOVE {assem=_, src=src, dst=dst} =>
                        populateFG(instrs, nodes, {control= #control fg,
                                                   def=Graph.Table.enter(#def fg, n, [dst]),
                                                   use=Graph.Table.enter(#use fg, n, [src]),
                                                   ismove= Graph.Table.enter(#ismove fg, n, true)})

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

        fun createEdges([], [], _, _, _) = ()
          | createEdges(i::instrs, n::nodes, iinstrs, nnodes, fg: Flow.flowgraph) =
              (case i
                of A.OPER{assem=_, src=_, dst=_, jump=jump} =>
                         (case jump
                          of NONE => ()
                           | SOME labs => makeEdges(n, labs, iinstrs, nnodes, #control fg))
                 | _ => ()
                 ;
               createEdges(instrs, nodes, iinstrs, nnodes, fg))

    fun instrs2graph instrs =
        let val fg: Flow.flowgraph = {
                                control = Graph.newGraph(),
                                def = Graph.Table.empty,
                                use = Graph.Table.empty,
                                ismove = Graph.Table.empty}
            val nodes = createNodes(instrs, #control fg)
            val newFg = populateFG(instrs, nodes, fg)
        in createEdges(instrs, nodes, instrs, nodes, newFg);
           (newFg, nodes)
        end
end
