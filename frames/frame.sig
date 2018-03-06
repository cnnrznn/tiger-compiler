signature FRAME =
sig 
        type frame
        type access
        val newFrame : {name: Temp.label,
                        formals: bool list} -> frame
        val name : frame -> Temp.label
        val formals : frame -> access list
        vall allocLocal : frame -> bool -> access
end
