structure MipsFrame : FRAME =
struct

        datatype access = InFrame of int | InReg of Temp.temp

        type frame = {  label: Temp.label,
                        formals: access list
                        (* other things *)
                        }

        fun newFrame {name: Temp.label,
                        formals: bool list}: frame =
                let val f' = true :: formals
                   fun formals2acc(_, []) = []
                     | formals2acc(off, f :: flist) =
                        let val acc = if f then (off := !off + 4;
                                                Inframe(!off))
                                      else Temp.newTemp
                        in acc :: formals2acc(off, flist)
                        end
                in frame{ label=name, formals=formals2acc(ref ~4, f') }
                end

end
