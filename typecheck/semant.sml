structure Semant =
struct

datatype envent = VarEnt of Types.ty
                | Funent of { params: Types.ty list, res: Types.ty }


fun transProg exp =
        let
                (*val env_t = Types.ty Symbol.table*)
                val env_v : envent Symbol.table
        in
                PrintAbsyn.print(TextIO.stdOut, exp);
                ()
        end
end
