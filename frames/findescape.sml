signature FINDESCAPE =
sig val findEscape: Absyn.exp -> unit
end

structure FindEscape =
struct
        type depth = int
        type escEnv = (depth * bool ref) Symbol.table

        fun seq2exps([]) = []
          | seq2exps((exp, pos)::seqexp) = (
                exp :: seq2exps(seqexp)
                )

        fun fields2exps([]) = []
          | fields2exps((_, exp, _) :: fields) = (
                exp :: fields2exps(fields)
                )

        fun traverseExpList(_, _, []) = ()
          | traverseExpList(env:escEnv, d:depth, exp::explist) = (
                traverseExp(env, d, exp);
                traverseExpList(env, d, explist)
                )
        and traverseVar(env:escEnv, d:depth, s:Absyn.var): unit = (
                )
        and traverseDecs(env:escEnv, d:depth, s:Absyn.dec list): escEnv = (
                        env (* TODO *)
                )
        and traverseExp(env:escEnv, d:depth, s:Absyn.exp): unit =
                case s
                 of A.VarExp var => traverseVar(env, d, var)
                  | A.CallExp {func=_, args=exps, pos=_} =>
                        traverseExpList(env, d, exps)
                  | A.OpExp {left=expl, oper=_, right=expr, pos=_} =>
                        traverseExpList(env, d, [expl, expr])
                  | A.RecordExp {fields, typ, pos} =>
                        traverseExpList(env, d, fields2exps(fields))
                  | A.SeqExp seqexp =>
                        traverseExpList(env, d, seq2exps(seqexp))
                  | A.AssignExp {var=v, exp=exp1, pos=_} => (
                        traverseVar(env, d, v);
                        traverseExp(env, d, exp1)
                        )
                  | A.IfExp {test=exp1, then'=exp2, else'=exp3, pos=_} => (
                        traverseExp(env, d, exp1);
                        traverseExp(env, d, exp2);
                        case exp3
                         of SOME exp => traverseExp(env, d, exp)
                          | NONE => ()
                        )
                  | A.WhileExp {test=exp1, body=exp2, pos=_} => (
                        traverseExp(env, d, exp1);
                        traverseExp(env, d, exp2)
                        )
                  | A.ForExp {var=v, escape=esc, lo=exp1, hi=exp2, body=exp3, pos=_} => (
                        traverseExp(env, d, exp1);
                        traverseExp(env, d, exp2);
                        let val env' = Symbol.enter(env, v, (d, esc))
                        in traverseExp(env', d+1, exp3)
                        end
                        )
                  | A.LetExp {decs=decs, body=body, pos=_} =>
                        let val env' = traverseDecs(env, d, decs)
                        in traverseExp(env', d+1, body)
                        end
                  | A.ArrayExp {typ=_, size=exp1, init=exp2, pos=_} => (
                        traverseExp(env, d, exp1);
                        traverseExp(env, d, exp2)
                        )
                  | _ => (* we dont care about other types of expressions *)
                         ()



        fun findEscape(prog:Absyn.exp): unit =
                let val env: escEnv = Symbol.empty
                in traverseExp(env, 0, prog)
                end
end

structure FE = FindEscape
