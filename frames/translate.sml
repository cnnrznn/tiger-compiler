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

        fun newLevel{parent=levp, name: Temp.label, formals: bool list} = (
                )

        (********************************************************)
        (* Create a new access for a variable given the level   *)
        (* and a bool indicating whether the variable escapes   *)
        (* the current frame. If it doesn not (esc is false)    *)
        (* then allocate a Temp.temp. Otherwise, allocate       *)
        (* InFrame.                                             *)
        fun allocLocal (lev:level) (esc:bool) =
                (lev, if esc then
                      else)
end
