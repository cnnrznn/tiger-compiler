CM.make "sources.cm";

let val prog = Semant.transProg(Parse.parse "test1.tig")
in PrintAbsyn.print(TextIO.stdOut, prog)
end
