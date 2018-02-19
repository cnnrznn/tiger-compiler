structure Semant =
struct

datatype envent = VarEnt of Types.ty
                | FunEnt of { params: Types.ty list, res: Types.ty }

fun transProg exp =
        let
                val tenv : envent Symbol.table = Symbol.empty
                val venv : envent Symbol.table = Symbol.empty

                (* add base environment *)
                val tenv = Symbol.enter(tenv, Symbol.symbol "string", VarEnt Types.STRING);
                val tenv = Symbol.enter(tenv, Symbol.symbol "int", VarEnt Types.INT);

                val venv = Symbol.enter(venv, Symbol.symbol "print",    FunEnt {params=[Types.STRING], res=Types.UNIT});
                val venv = Symbol.enter(venv, Symbol.symbol "flush",    FunEnt {params=[], res=Types.UNIT});
                val venv = Symbol.enter(venv, Symbol.symbol "getchar",  FunEnt {params=[], res=Types.STRING});
                val venv = Symbol.enter(venv, Symbol.symbol "ord",      FunEnt {params=[Types.STRING], res=Types.INT});
                val venv = Symbol.enter(venv, Symbol.symbol "chr",      FunEnt {params=[Types.INT], res=Types.STRING});
                val venv = Symbol.enter(venv, Symbol.symbol "size",     FunEnt {params=[Types.STRING], res=Types.INT});
                val venv = Symbol.enter(venv, Symbol.symbol "substring",FunEnt {params=[Types.STRING, Types.INT, Types.INT], res=Types.STRING});
                val venv = Symbol.enter(venv, Symbol.symbol "concat",   FunEnt {params=[Types.STRING, Types.STRING], res=Types.STRING});
                val venv = Symbol.enter(venv, Symbol.symbol "not",      FunEnt {params=[Types.INT], res=Types.INT});
                val venv = Symbol.enter(venv, Symbol.symbol "exit",     FunEnt {params=[Types.INT], res=Types.UNIT});
        in
                (* recurse *)
                ()
        end
end
