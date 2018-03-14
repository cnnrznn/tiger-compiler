signature TRANSLATE =
sig
	type level
	type access (* not the same as Frame.access *)

	val outermost : level
	val newLevel : {parent: level, name: Temp.label,
	    	       	formals: bool list} -> level
	val formals: level -> access list
	val allocLocal: level -> bool -> access
end

structure Translate : TRANSLATE =
struct
        type level = int
        type access = level * Frame.access

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
end
