structure Main = struct

   structure Tr = Translate
   structure F = Frame

 fun getsome (SOME x) = x

   fun emitproc out (F.PROC{body,frame}) =
     let val _ = print ("emit " ^ Symbol.name ( Frame.name frame) ^ "\n")
(*         val _ = Printtree.printtree(out,body); *)
	 val stms = Canon.linearize body
(*         val _ = app (fn s => Printtree.printtree(out,s)) stms; *)
         val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	 val instrs =   List.concat(map (MipsGen.codegen frame) stms') 
         val instrs = Frame.procEntryExit2 (frame,instrs)
         
         val (instrs, alloc) =  RegAlloc.alloc (instrs, frame)
         val {prolog=prolg, body=instrs, epilog=epilg} = Frame.procEntryExit3(frame, instrs)
         val alloc_list = List.map (fn (k,v) => Temp.makestring k ^" , " ^ v ^ "\n") (IntBinaryMap.listItemsi(alloc))


         fun getAllocatedRegister alloc t =
             case Temp.Table.look(alloc,t) of
             SOME(c) => "$"^c
             | NONE => "$" ^ (Frame.makeString t)

         val format0 = Assem.format(getAllocatedRegister alloc)

      in print "==========================================\n";
         (*Translate.printTreeSTM body; *)
         print "*************************\n";
        (* app (fn i => TextIO.output(TextIO.stdOut,format0 i)) instrs; *)
         print "*************************\n";
         TextIO.output (TextIO.stdOut,  "\n*** register allocation *** \n");
         app (fn i => TextIO.output(TextIO.stdOut, i^ "  ")) alloc_list;
         TextIO.output (TextIO.stdOut, "\n");
         print "==========================================\n\n";
         app (fn i => TextIO.output(out,format0 i)) instrs
     end
    | emitproc out (F.STRING(lab,s)) = (
        print ("\temitting string" ^ s);
        TextIO.output(out, F.string(lab,s))
        )

   fun withOpenFile fname f = 
       let val out = TextIO.openOut fname
        in (f out before TextIO.closeOut out) 
	    handle e => (TextIO.closeOut out; raise e)
       end 

   fun compile filename = 
       let val absyn = Parse.parse filename
           val frags = (FindEscape.findEscape absyn; Semant.transProg absyn)
        in 
            withOpenFile (filename ^ ".s") 
	     (fn out => (app (emitproc out) frags))
       end

end



