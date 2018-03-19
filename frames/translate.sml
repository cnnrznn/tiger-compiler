signature TRANSLATE =
sig
	type level
	type access (* not the same as Frame.access *)
        type exp

	val outermost : level
	val newLevel : {parent: level, name: Temp.label,
	    	       	formals: bool list} -> level
	val formals: level -> access list
	val allocLocal: level -> bool -> access

        val simpleVar: access * level -> exp
        val subscriptVar : exp * exp -> exp
        val fieldVar: exp * int -> exp
end

structure Translate : TRANSLATE =
struct
        type level = {parent : level, frame : Frame.frame, unique : unit ref}
        type access = level * Frame.access

        datatype exp = Ex of Tree.exp
             | Nx of Tree.stm
             | Cx of Temp.label * Temp.label -> Tree.stm

        val outermost = 0
        val nextLevel = ref 0

        (********************************************************)
        (* A comment should explain this block of code.         *)

        structure Table = IntMapTable(type key=level
                                fun getInt level = level)
        val HT : Frame.frame Table.table ref = ref Table.empty

        fun init () =
                let val frame = Frame.newFrame{name=Temp.newlabel(), formals=[]}
                    val HT' = Table.enter(!HT, outermost, frame)
                in HT := HT'
                end
        (********************************************************)

        fun newLevel{parent=plev, name: Temp.label, formals: bool list} =
                let val frame = Frame.newFrame{name = name,
                                                formals = true :: formals}
                in nextLevel := !nextLevel + 1;
                   (* create mapping from nextLevel -> frame *)
                   HT := Table.enter(!HT, !nextLevel, frame);
                   !nextLevel
                end

        (********************************************************)
        (* Create a new access for a variable given the level   *)
        (* and a bool indicating whether the variable escapes   *)
        (* the current frame. If it doesn not (esc is false)    *)
        (* then allocate a Temp.temp. Otherwise, allocate       *)
        (* InFrame.                                             *)
        fun allocLocal (lev:level) (esc:bool) =
                let val frame = case Table.look(!HT, lev)
                                 of SOME f => f
                                  | NONE => (ErrorMsg.error 0 "should never see this";
                                                {label=Temp.newlabel(),
                                                 formals=[],
                                                 nextOffset=ref 4
                                                })
                    val acc = Frame.allocLocal(frame)(esc)
                in (lev, acc)
                end

        fun formals level =
                case Table.look(!HT, level)
                 of SOME frame => let fun makeList(_, []) = []
                                    | makeList(level, formal :: formals) =
                                        (level, formal) :: makeList(level, formals)
                              in makeList(level, #formals frame)
                              end
                  | NONE => (ErrorMsg.error 0 "should never see this";
                                [])
        (***********************************************************************)
        (* This method starts from the current level and follows the static    *)
        (* links to get to parent level frames until it reaches the declaration*)
        (* level of the variable. At each level it adds the static link offset *)
        (* to the frame pointer and finally returns a tree                     *)

        fun followStaticLinks (frAccess:Frame.access, varLevel:level, curLevel: level) =
           let 
               val parentLevel = #parent curLevel
               val frame =  #frame curLevel
               val sl_access :: formals = Frame.formals(frame)
                 
           in
               if #unique curLevel = #unique varLevel then
                   Tree.TEMP(Frame.FP)
               else
                   Frame.exp (frAccess) followStaticLinks (sl_access ,varLevel, parentLevel)
           end
	
        (*****************************************)
        (* function to translate simple variable *)
     
	    
        fun simpleVar(acc : access, lev : level) = 
 	    let
		val varLevel = #1 acc
                val frAccess = #2 acc 
            in
                (* following static links implemented*)
		(*Ex(Frame.exp (frAccess) (Tree.TEMP(Frame.FP)) )  *)
                Ex(followStaticLinks(frAccess, varLevel, level) )
            end
        
        (*****************************************)
        (* function to translate array subscript variable *)
    
       fun subscriptVar(varExp: Frame.exp, indexExp: Frame.exp) =
          (* doubts - should we use UnEx constructor for the xpressions? is it Tree.PLUS or Tree.MINUS ? *)
          EX( Tree.MEM( Tree.BINOP( Tree.PLUS, varExp, Tree.BINOP( Tree.MUL,  indexExp , Tree.CONST (Frame.wordSize) ) )))

       
       (*****************************************)
       (* function to translate record field variable *)
     
       fun fieldVar (varExp : Frame.exp, fieldIndex : int) =
           Ex( Tree.MEM ( Tree.BINOP ( Tree.PLUS, varExp , Tree.CONST(fieldIndex * Frame.wordSize) ) ) )
           
	     
end
