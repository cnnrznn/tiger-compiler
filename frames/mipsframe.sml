structure MipsFrame : FRAME =
struct

        datatype access = InFrame of int | InReg of Temp.temp

        type frame = {  label: Temp.label,
                        formals: access list
                        nextOffset: int ref
                        (* other things *)
                        }

        fun formals(f:frame) = #formals f

        fun name(f: frame) = #label f

        fun newFrame({name: Temp.label,
                        formals: bool list}): frame =
                let val f' = true :: formals
                    val off = ref 4
                   fun formals2acc(_, []) = []
                     | formals2acc(off, f :: flist) =
                        let val acc = if f then (off := !off - 4;
                                                Inframe(!off))
                                      else Temp.newTemp
                        in acc :: formals2acc(off, flist)
                        end
                in frame{ label=name,
                          formals=formals2acc(off, f'),
                          nextOffset=off }
                end

        fun allocLocal (f: frame) (esc: bool) =
                let val off = #nextOffset f
                in if esc then
                        (off := !off - 4;
                        InFrame(off))
                   else Temp.newTemp

end
