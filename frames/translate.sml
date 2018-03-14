signature TRANSLATE =
sig
	type level
	type accesss (* not the same as Frame.access *)

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
        val HT = ref Frame.frame Table.empty

        fun init =
                let val frame = Frame.newFrame(Temp.newLabel, [])
                    val HT' = Table.enter(!HT, outermost, frame)
                in HT := HT'
                end
        (********************************************************)

        fun newLevel{parent=plev, name: Temp.label, formals: bool list} =
                let val frame = Frame.newFrame(name,
                                                formals = true :: formals)
                in nextLevel := !nextLevel + 1;
                   (* create mapping from nextLevel -> frame *)
                   HT := Table.enter(!HT, !nextLevel, frame);
                   nextLevel
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
                                  | NONE => (ErrorMsg.error "should never see this"; Frame.frame)
                    val acc = Frame.allocLocal(frame, esc)
                in (lev, acc)
                end
end
