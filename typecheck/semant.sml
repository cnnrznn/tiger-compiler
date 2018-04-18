structure Semant =
struct

type expty = {exp: Translate.exp, ty: T.ty}

datatype envent = VarEnt of { access: Translate.access,
                              ty: T.ty }
                | FunEnt of { level: Translate.level,
                              label: Temp.label,
                              params: T.ty list,
                              res: T.ty }

val loopLevel = ref 0

(********************************************************)
(* Function for translating a NAME into a different     *)
(* type                                                 *)
fun actual_ty ty =
        case ty
         of T.NAME(_, tyopref) => (
                case !tyopref
                 of SOME ty' => actual_ty ty'
                  | NONE => (ErrorMsg.error 0 "error translating type pseudonym";
                             T.INT)
                )
          | ty' => ty'

(********************************************************)
(* Walk through a Record's field list, looking for      *)
(* symbol 'id2'. If it's in the list, return it's type. *)
(* If not, return T.INT.                            *)

fun findFieldType(T.RECORD((id1, ty)::rest, u), id2, fieldIndex, pos) =
        if id1 = id2 then { index = fieldIndex , ty = actual_ty ty}
        else findFieldType(T.RECORD(rest, u), id2, fieldIndex + 1, pos)
  | findFieldType(T.RECORD([], u), id2 , fieldIndex , pos) =
        (ErrorMsg.error pos ("Unable to find symbol " ^
                                S.name id2 ^
                                " in record");
        { index = ~1 , ty = T.INT}
        )

(********************************************************)
(* Functions for checking legal declaration and         *)
(* expression type pairings                             *)

fun checkDecType(T.RECORD(_, u1), T.RECORD(_, u2)) = u1 = u2
  | checkDecType(T.RECORD(_, _), T.NIL) = true
  | checkDecType(T.INT, T.INT) = true
  | checkDecType(T.STRING, T.STRING) = true
  | checkDecType(T.ARRAY(_, u1), T.ARRAY(_, u2)) = u1 = u2
  | checkDecType(_, _) = false

fun checkSame(T.RECORD(_, u1), T.RECORD(_, u2)) = u1 = u2
  | checkSame(T.RECORD(_, _), T.NIL) = true
  | checkSame(T.NIL, T.RECORD(_, _)) = true
  | checkSame(T.INT, T.INT) = true
  | checkSame(T.STRING, T.STRING) = true
  | checkSame(T.ARRAY(_, u1), T.ARRAY(_, u2)) = u1 = u2
  | checkSame(T.UNIT, T.UNIT) = true
  | checkSame(_, _) = false

(********************************************************)


(********************************************************)
(* These functions are used to check the left and       *)
(* right sides of arithmetic operations.                *)

fun checkInts(T.INT, T.INT, _) =
        ()
  | checkInts(_, _, pos) =
        (ErrorMsg.error pos "integer operands required";
        ())

fun checkIntsOrStrings(T.INT, T.INT, _) =
        ()
  | checkIntsOrStrings(T.STRING, T.STRING, _) =
        ()
  | checkIntsOrStrings(_, _, pos) =
        (ErrorMsg.error pos "integer or string operands required";
        ())

fun checkIntsStrsRecsArrs(T.INT, T.INT, _) =
        ()
  | checkIntsStrsRecsArrs(T.STRING, T.STRING, _) =
        ()
  | checkIntsStrsRecsArrs(T.RECORD(_, u1), T.RECORD(_, u2), pos) =
        (if u1 = u2 then ()
         else
                (ErrorMsg.error pos "record types don't match";
                ())
        )
  | checkIntsStrsRecsArrs(T.ARRAY(_, u1), T.ARRAY(_, u2), pos) =
        (if u1 = u2 then ()
         else
                (ErrorMsg.error pos "array types don't match";
                ())
        )
  | checkIntsStrsRecsArrs(T.NIL, T.RECORD(_, _), _) = ()
  | checkIntsStrsRecsArrs(T.RECORD(_, _), T.NIL, _) = ()
  | checkIntsStrsRecsArrs(_, _, pos) =
        (ErrorMsg.error pos "integer, string, array, or record operands required";
        ())

(*******************************************************)

fun transOpExp(tenv, venv, A.OpExp{left, oper, right, pos},
                        level: Translate.level, doneLabel) =
        let
                val {exp=expl, ty=tyLeft} = transExp(tenv, venv, left, level, doneLabel)
                val {exp=expr, ty=tyRight} = transExp(tenv, venv, right, level, doneLabel)
                (* val atl = actual_ty tyLeft
                val atr = actual_ty tyRight *)
        in
        case oper of
              (A.EqOp | A.NeqOp) => (
                checkIntsStrsRecsArrs(tyLeft, tyRight, pos)
                )
            | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) => (
                checkIntsOrStrings(tyLeft, tyRight, pos)
                )

            | (A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp) => (
                checkInts(tyLeft, tyRight, pos)
                );
        {exp=Translate.binop(oper, expl, expr), ty=T.INT}
        end

(*******************************************************)
and checkFunctionArgs(tenv, venv,(tyFormal::restFormal), res, (exp::restActual), argList, pos,
                        level: Translate.level, doneLabel) =
	(let
		val {exp= argExp , ty = tyExp} = transExp(tenv, venv, exp, level, doneLabel)
	 in
		if checkDecType(actual_ty tyFormal, tyExp) then
			checkFunctionArgs(tenv, venv,restFormal, res, restActual, argExp::argList, pos, level, doneLabel)
		else
			(ErrorMsg.error pos ("Type Mismatch in args");
                        {argExps =[] , tychk =false})	
	 end
	)
 | checkFunctionArgs(tenv, venv,[], res, [], argList, pos, _, _) = {argExps = argList , tychk =true}
 | checkFunctionArgs(tenv, venv,_,res,_, _, pos, _, _) =(ErrorMsg.error pos ("Incomplete arguments in the function call"); {argExps =[] , tychk =false})

and transCallExp(tenv, venv, A.CallExp {func,args, pos},
                        level: Translate.level, doneLabel) =
	(case S.look(venv,func)
		of SOME (FunEnt{level=funLevel, label=funLabel, params=params, res=res}) =>
                       let
                          val {argExps =argExps , tychk = tychk} = checkFunctionArgs(tenv, venv, params, res, args,[], pos, level, doneLabel)
                       in
                           if tychk then
                               {exp=Translate.callExp(funLevel, level, funLabel, argExps), ty=res}
			   else ({exp=Translate.errorTree(3), ty = T.INT})
                       end		 
		| _ => (ErrorMsg.error pos ("undeclared function " ^ S.name func);
                        {exp=Translate.errorTree(3), ty=T.INT})
	)
(********************************************************)
(* FUnction to check if the record creation is legal by *)
(* walking through the record fields and matching the   *)
(* names and and types.                                 *) 

and checkRecordFields(tenv,venv,T.RECORD((id1, tyRec)::rest, u), ((id2,expRec,posF)::restFields), pos, fields,
                        level: Translate.level, doneLabel) =
	let
		val {exp=e , ty=tyExp} = transExp(tenv, venv, expRec, level, doneLabel)
	in
		if id1 = id2 then
			if checkDecType(actual_ty tyRec, actual_ty tyExp) then
				checkRecordFields(tenv, venv, T.RECORD(rest, u), restFields, pos, e::fields, level, doneLabel)
			else
				(ErrorMsg.error posF ("type mismatch in record field " ^ S.name id1);
				 {fieldList = [], tychk = false})
		else (ErrorMsg.error posF ("field names incorrect" ^ S.name id1);
                {fieldList = [], tychk = false})
	end
  | checkRecordFields(tenv, venv, T.RECORD([], u), [], pos,fields, _, _) = {fieldList=fields, tychk=true}
  | checkRecordFields(tenv,venv, _ , _ , pos,fields, _, _) = (ErrorMsg.error pos ("mismatched field names");
								 {fieldList = [], tychk = false})
and transRecordExp(tenv, venv, A.RecordExp{fields,typ, pos},
                        level: Translate.level, doneLabel) =
	case S.look(tenv,typ)
		of SOME ty => (
                        let val recty = actual_ty ty
                            val {fieldList=fieldList, tychk=tychk} =
                                        checkRecordFields(tenv, venv, recty, fields,  pos, [], level, doneLabel)
                        in
                                if tychk then
                                        {exp=Translate.recordExp(fieldList), ty = recty}
                                else
                                        {exp=Translate.errorTree(0), ty = T.INT}
                        end
		)
		| _ =>  (ErrorMsg.error pos ("undefined type " ^ S.name typ);
                        {exp=Translate.errorTree(5), ty=T.INT})

(*******************************************************)

and transSeqExp(tenv, venv, A.SeqExp ((exp, pos)::(onemore::rest)),
                        level: Translate.level, doneLabel, expList) =
        let val {exp=expOne, ty=_} = transExp(tenv, venv, exp, level, doneLabel)
        in transSeqExp(tenv, venv, A.SeqExp(onemore::rest), level, doneLabel, expList @ [expOne])
        end
  | transSeqExp(tenv, venv, A.SeqExp ((exp, pos)::[]),
                        level: Translate.level, doneLabel, expList) =
        let val {exp=expOne, ty=tyexp} = transExp(tenv, venv, exp, level, doneLabel)
        in {exp=Translate.seqExp(expList, expOne), ty=tyexp}
        end
	
(*******************************************************)

and transAssignExp(tenv, venv, A.AssignExp{var,exp, pos},
                        level: Translate.level, doneLabel) =
	let 
		val {exp=expVar, ty=tyVar} = transVarExp(tenv, venv, var, level, doneLabel)
		val {exp=expInit, ty=tyExp} = transExp(tenv, venv, exp, level, doneLabel)
	in
		if checkDecType(tyVar, tyExp) then
                                ()
		else (  ErrorMsg.error pos "type mismatch";
                                ());
                {exp=Translate.assignExp(expVar, expInit), ty=T.UNIT}
	end

(*******************************************************)

and transIfExp(tenv, venv, A.IfExp{test, then', else', pos},
                        level: Translate.level, doneLabel) =
        let
                val {exp=expTest, ty=tyTest} = transExp(tenv, venv, test, level, doneLabel)
                val {exp=expThen, ty=tyThen} = transExp(tenv, venv, then', level, doneLabel)
        in 
                if tyTest = T.INT then
                        case else'
                        of SOME e =>
                                let val {exp=expElse, ty=tyElse} = transExp(tenv, venv, e, level, doneLabel)
                                in
                                        if checkSame(tyThen, tyElse) then(
                                          let val ty=
                                                case tyThen
                                                  of T.NIL => tyElse
                                                  | _ => tyThen
                                          in {exp=Translate.ifThenElse(expTest, expThen, expElse),
                                                ty=ty}
                                          end
                                        )
                                        else (ErrorMsg.error pos "type mismatch";
                                              {exp=Translate.errorTree(1), ty=T.UNIT})
                                end
                        | NONE => {exp=Translate.ifThen(expTest,expThen), ty=T.UNIT}
                else
                        (ErrorMsg.error pos "Test is not integer value";
                        {exp=Translate.errorTree(1), ty=T.UNIT})
        end

(*******************************************************)
(* Does produce no value means T.UNIT? *)
and transWhileExp(tenv, venv, A.WhileExp {test, body, pos},
                        level: Translate.level, doneLabel) =
	let
		val {exp=expTest, ty=tyTest} = transExp(tenv, venv, test, level, doneLabel)
	in loopLevel := !loopLevel + 1;
		let
                        val labDone = Temp.newlabel()
                        val labBody = Temp.newlabel()
                        val labTest = Temp.newlabel()
			val {exp=expBody , ty=tyBody} = transExp(tenv, venv, body, level, SOME labDone)
		in
                        loopLevel := !loopLevel - 1;
                        case (tyTest, tyBody)
                                of (T.INT,T.UNIT) => (T.UNIT)
                                | (T.INT,_)		 =>(ErrorMsg.error pos "Body must produce no value";
                                                                        T.UNIT)
                                | (_, T.UNIT)		 => (ErrorMsg.error pos "Test is not integer value";
                                                        T.UNIT);
                        {exp=Translate.whileExp(labDone, labBody, labTest, expBody, expTest),
                        ty=T.UNIT}
                end
	end

(*******************************************************)

and transForExp(tenv, venv, A.ForExp {var, escape, lo, hi, body, pos},
                level: Translate.level, doneLabel) =
	let 
		val {exp=expLo, ty=tyLo} = transExp(tenv, venv, lo, level, doneLabel)
		val {exp=expHi, ty=tyHi} = transExp(tenv, venv, hi, level, doneLabel)

                val labDone = Temp.newlabel()
                val venv' = S.enter(venv, var, VarEnt{access=Translate.allocLocal(level)(!escape),
                                              ty=T.INT})
                val {exp=expIndx, ty=_} = transVarExp(tenv, venv', A.SimpleVar(var, 0), level, doneLabel)
	in
		case (actual_ty tyLo, actual_ty tyHi)
		of (T.INT, T.INT) =>
			(loopLevel := !loopLevel + 1;
			let 
				val {exp=expBody, ty=tyBody} = transExp(tenv, venv', body, level, SOME labDone)
			in
				loopLevel := !loopLevel - 1;
				case tyBody
				of T.UNIT => T.UNIT
				| _ => (ErrorMsg.error pos "Body must produce no value";
								T.UNIT);
                                {exp=Translate.forExp(expIndx, expLo, expHi, expBody, labDone), ty=T.UNIT}
			end)
		| (_, _) => (ErrorMsg.error pos "lo/hi expressions must be integer value";
				{exp=Translate.errorTree(7), ty=T.UNIT})
	end

(*******************************************************)

and transBreakExp(tenv, venv,  A.BreakExp pos, level: Translate.level) =
	( if !loopLevel = 0 then
		(ErrorMsg.error pos "Illegal break. No enclosing While/For loop";
								T.UNIT)
	  else (T.UNIT)
	)

(*******************************************************)

and transArrayExp(tenv, venv, A.ArrayExp {typ,size,init,pos},
                        level: Translate.level, doneLabel) = (
        case S.look(tenv,typ) of
          SOME (ty) => (
                let
                        val arrty = actual_ty ty
                        val T.ARRAY(itemty, _) = arrty
                        val {exp= sizeExp , ty=tySize} = transExp(tenv, venv, size, level, doneLabel)
                        val {exp= initExp , ty=tyInit} = transExp(tenv, venv, init, level, doneLabel)
                in
                        if actual_ty(tySize) = T.INT then
                                if checkDecType(itemty, tyInit) then
                                        {exp = Translate.arrayExp(sizeExp, initExp) ,ty = arrty}
                                else (  ErrorMsg.error pos ("type mismatch " ^ S.name typ) ;
					{exp=Translate.errorTree(0), ty = T.INT})
                        else
                                (ErrorMsg.error pos ("Array Size must be an Integer ");
				{exp=Translate.errorTree(0), ty = T.INT})
                end
                )
        | _ => (ErrorMsg.error pos ("undefined type " ^ S.name typ);
               {exp=Translate.errorTree(0), ty = T.INT})
        )
(*******************************************************)

and transVarExp(tenv, venv, A.SimpleVar(id,pos),
                        level: Translate.level, doneLabel) =
        (case Symbol.look(venv, id)
         of SOME (VarEnt{access= acc, ty= typ}) => { exp = Translate.simpleVar (acc, level), ty = actual_ty typ}
          | NONE => (ErrorMsg.error pos ("undefined variable " ^
                                                S.name id);
                        {exp=Translate.errorTree(9), ty = T.INT})
        )
  | transVarExp(tenv, venv, A.FieldVar(var, id, pos),
                        level: Translate.level, doneLabel) =
       let
           val {exp=expVar , ty=tyVar} = transVarExp(tenv, venv, var, level, doneLabel)
        in
            case tyVar
             of T.RECORD record => (  
                 let 
                     val {index=index, ty=ty}  = findFieldType(T.RECORD record, id, 0, pos)
                 in
                    {exp = Translate.fieldVar(expVar, index) , ty=ty}
                 end
                 )
              | _ => (ErrorMsg.error pos "Accessing a field in non-record type";
                        {exp=Translate.errorTree(8), ty =T.INT} )
        end
  | transVarExp(tenv, venv, A.SubscriptVar(var, exp, pos),
                        level: Translate.level, doneLabel) =  
        let 
            val {exp=expVar , ty=tyVar} = transVarExp(tenv, venv, var, level, doneLabel) 
        in
            case tyVar
             of T.ARRAY(arrty, unique) =>
                let val {exp = indexExp , ty=tyexp} = transExp(tenv, venv, exp, level, doneLabel)
                in
                  case tyexp
                    of T.INT => {exp=Translate.subscriptVar(expVar, indexExp), ty=actual_ty arrty}
                     | _ => (ErrorMsg.error pos "Array index must be of type INT";
                                   { exp=Translate.errorTree(4), ty=T.INT})
                end

              | _ => (ErrorMsg.error pos "Accessing subscript of non-array type";
                       { exp =Translate.errorTree(4), ty=T.INT})
        end
        

(*******************************************************)

and transTy(tenv, A.NameTy(sym, pos)) =
        (case S.look(tenv, sym) of
          SOME t => t
        | NONE => (ErrorMsg.error pos "type not defined in this scope";
                   T.INT)
        )
  | transTy(tenv, A.RecordTy(fields)) =
        let fun fields2types({name, escape, typ, pos}::rest) =
                (case S.look(tenv, typ) of
                   SOME t => (name, t) :: fields2types(rest)
                 | NONE => (ErrorMsg.error pos "field type not defined in scope";
                        (name, T.INT) :: fields2types(rest))
                )
              | fields2types([]) = []
        in T.RECORD(fields2types(fields), ref ())
        end
  | transTy(tenv, A.ArrayTy(sym, pos)) =
        case S.look(tenv, sym) of
          SOME t => T.ARRAY(t, ref ())
        | NONE => (ErrorMsg.error pos "array type not defined in scope";
                   T.ARRAY(T.INT, ref ()))

and transVarDec(tenv, venv, A.VarDec{name, escape, typ, init, pos},
                level: Translate.level, doneLabel) =
        let val {exp=expInit, ty=tyexp} = transExp(tenv, venv, init, level, doneLabel)
            val access=Translate.allocLocal(level)(!escape)
        in
        case typ
         of SOME(id, p) => (
                case Symbol.look(tenv, id)
                 of SOME typ =>
                        if checkDecType(actual_ty typ, actual_ty tyexp) then
                                ({te=tenv, ve=S.enter(venv, name,
                                                VarEnt{access=access,
                                                       ty=tyexp})},
                                Translate.assignment(access, expInit, level))
                        else (  ErrorMsg.error p "type mismatch";
                                ({te=tenv, ve=venv}, Translate.errorTree(2))
                        )
                  | NONE => (   ErrorMsg.error p "type not defined";
                                ({te=tenv, ve=venv}, Translate.errorTree(2))
                        )
                )
          | NONE => ({te=tenv, ve=S.enter(venv, name, VarEnt{access=access, ty=tyexp})},
                        Translate.assignment(access, expInit, level))
        end

and transFunHed(tenv, venv, [], _) =
        {te=tenv, ve=venv}
  | transFunHed(tenv, venv, {name, params, result, body, pos}::fundecs, level: Translate.level) =
        let
          fun params2types([]) = []
            | params2types({name, escape, typ, pos}::rest) =
                (case S.look(tenv, typ) of
                   SOME t => (t :: params2types(rest))
                |  NONE => (ErrorMsg.error pos "function parameter of undefined type";
                            (T.INT :: params2types(rest)))
                )
          fun resTy(typ) = (
                case typ of
                  SOME (sym, pos) => (
                        case S.look(tenv, sym) of
                          SOME t => t
                        | NONE => (ErrorMsg.error pos "undeclared function return type";
                                   T.INT)
                        )
                | NONE => T.UNIT
                )
          fun params2bools([]) = []
          val newlabel = Temp.newlabel()
          val venv' = S.enter(venv, name, FunEnt{level=Translate.newLevel{parent=level,
                                                                          name=newlabel,
                                                                          formals=[]},
                                                 label=newlabel,
                                                 params=params2types(params),
                                                 res=resTy(result)})
        in transFunHed(tenv, venv', fundecs, level)
        end

and transFunBod(tenv, venv, A.FunctionDec [], _, doneLabel) = ()
  | transFunBod(tenv, venv, A.FunctionDec({name=name, params=paramsAbsyn, result=result, body=body, pos=pos}::fundecs), level: Translate.level, doneLabel) =
        let fun params2venv(venv, []) = venv
              | params2venv(venv, {name, escape, typ, pos}::params) = (
                        params2venv(S.enter(venv, name,
                                                VarEnt{access=Translate.allocLocal(level)(!escape),
                                                        ty=(case S.look(tenv, typ)
                                                         of SOME t => t
                                                          | NONE => (
                                                              ErrorMsg.error pos "unexpected error finding local variable type";
                                                              T.INT))}),
                                        params)
              )
        in
        ((case S.look(venv, name)
         of SOME(FunEnt{level=bodyLev, label=_, params=parambools, res=res}) =>
                        (let val venv' = params2venv(venv, paramsAbsyn)
                             val {exp=expBody, ty=_} = transExp(tenv, venv', body, bodyLev, doneLabel)
                        in Translate.procEntryExit{level=bodyLev, bodyExp=expBody}
                        end;
                        ())
          | _ => (ErrorMsg.error pos "should never see this (fun)";
                  ()
                ));
        transFunBod(tenv, venv, A.FunctionDec(fundecs), level, doneLabel)
        )
        end
  | transFunBod(_, _, _, _, _) =
        (ErrorMsg.error 0 "unexpected error"; ())

and transTypHed(tenv, venv, []) =
        {te=tenv, ve=venv}
  | transTypHed(tenv, venv, {name, ty, pos}::typedecs) =
        let val tenv' = S.enter(tenv, name, T.NAME(name, ref NONE))
        in transTypHed(tenv', venv, typedecs)
        end

and transTypBod(tenv, venv, []) = ()
  | transTypBod(tenv, venv, {name, ty, pos}::typedecs) =
        ((case S.look(tenv, name)
         of SOME(T.NAME(name, tyopref)) =>
                        tyopref := SOME(transTy(tenv, ty))
          | _ => (ErrorMsg.error pos "should never see this (type)";
                  ()
                ));
        transTypBod(tenv, venv, typedecs))

and transDecs(tenv, venv, A.VarDec dec::decs, level: Translate.level,
                explist: Translate.exp list, doneLabel) =
        let val ({te=tenv', ve=venv'}, exp) = transVarDec(tenv, venv, A.VarDec dec, level, doneLabel)
        in transDecs(tenv', venv', decs, level, explist @ [exp], doneLabel) end
  | transDecs(tenv, venv, A.TypeDec dec::decs, level: Translate.level,
                explist: Translate.exp list, doneLabel) =
        let val {te=tenv', ve=venv'} = transTypHed(tenv, venv, dec)
        in transTypBod(tenv', venv', dec);
           transDecs(tenv', venv', decs, level, explist, doneLabel)
        end
  | transDecs(tenv, venv, A.FunctionDec dec::decs, level: Translate.level,
                explist: Translate.exp list, doneLabel) =
        let val {te=tenv', ve=venv'} = transFunHed(tenv, venv, dec, level)
        in transFunBod(tenv', venv', A.FunctionDec dec, level, doneLabel);
           transDecs(tenv', venv', decs, level, explist, doneLabel)
        end
  | transDecs(tenv, venv, [], _, explist: Translate.exp list, doneLabel) =
        ({te=tenv, ve=venv}, explist)

(*******************************************************)

and transExp(tenv, venv, exp, level: Translate.level,
                doneLabel: Temp.label option) =
case exp of
  A.OpExp opexp =>(     (* print("transOpExp\n"); *)
        transOpExp(tenv, venv, A.OpExp opexp, level, doneLabel))
| A.VarExp var =>(      (* print("transVarExp\n"); *)
        transVarExp(tenv, venv, var, level, doneLabel))
| A.NilExp =>(          (* print("transNilExp\n"); *)
        {exp=Translate.nilExp(), ty=T.NIL})
| A.IntExp n =>(        (* print("transIntExp\n"); *)
        {exp=Translate.intExp(n), ty=T.INT})
| A.StringExp(str, p) =>(       (* print("transStringExp\n"); *)
        {exp=Translate.strExp(str), ty=T.STRING})
| A.CallExp callexp =>(         (* print("transCallExp\n"); *)
        transCallExp(tenv, venv, A.CallExp callexp, level, doneLabel))
| A.RecordExp recexp =>(        (* print("transRecordExp\n");*)
        transRecordExp(tenv, venv, A.RecordExp recexp, level, doneLabel))
| A.SeqExp seqexp =>(           (*print("transSeqExp\n");*)
        transSeqExp(tenv, venv, A.SeqExp seqexp, level, doneLabel, []))
| A.AssignExp assignexp =>(     (*print("transAssignExp\n");*)
        transAssignExp(tenv, venv, A.AssignExp assignexp, level, doneLabel))
| A.IfExp ifexp =>(             (*print("transIfExp\n");*)
        transIfExp(tenv, venv, A.IfExp ifexp, level, doneLabel))
| A.WhileExp whilexp =>(        (*print("transWhileExp\n");*)
        transWhileExp(tenv, venv, A.WhileExp whilexp, level, doneLabel))
| A.ForExp forexp =>(           (*print("transForExp\n");*)
        transForExp(tenv, venv, A.ForExp forexp, level, doneLabel))
| A.BreakExp breakexp =>(       (*print("transBreakExp\n");*)
        {exp=Translate.break(doneLabel), ty=actual_ty(transBreakExp(tenv, venv,  A.BreakExp breakexp, level))})
| A.LetExp {decs, body, pos} =>((*print("transLetExp\n");*)
        let val ({te=tenv', ve=venv'}, explist: Translate.exp list) =
                        transDecs(tenv, venv, decs, level, [], doneLabel)
            val {exp=exp, ty=ty} = transExp(tenv', venv', body, level, doneLabel)
        in  {exp=Translate.prepend(explist, exp), ty=ty}
        end)
| A.ArrayExp arrexp =>(         (*print("transArrayExp\n");*)
        transArrayExp(tenv, venv, A.ArrayExp arrexp, level, doneLabel))

(*******************************************************)

and transProg(exp) =
        (* initialize Translate structure *)
        (Translate.init();

        let
                val tenv : T.ty Symbol.table = Symbol.empty
                val venv : envent Symbol.table = Symbol.empty

                (* add base environment *)
                val tenv = Symbol.enter(tenv, Symbol.symbol "string", T.STRING)
                val tenv = Symbol.enter(tenv, Symbol.symbol "int", T.INT)

                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "print",    FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[false]},
                                                                                label=newlabel,
                                                                                params=[T.STRING],
                                                                                res=T.UNIT})
                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "flush",    FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[]},
                                                                                label=newlabel,
                                                                                params=[T.UNIT],
                                                                                res=T.UNIT})
                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "getchar",  FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[]},
                                                                                label=newlabel,
                                                                                params=[T.UNIT],
                                                                                res=T.STRING})
                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "ord",      FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[false]},
                                                                                label=newlabel,
                                                                                params=[T.STRING],
                                                                                res=T.INT})
                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "chr",      FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[false]},
                                                                                label=newlabel,
                                                                                params=[T.INT],
                                                                                res=T.STRING})
                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "size",     FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[false]},
                                                                                label=newlabel,
                                                                                params=[T.STRING],
                                                                                res=T.INT})
                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "substring",FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[false, false, false]},
                                                                                label=newlabel,
                                                                                params=[T.STRING, T.INT, T.INT],
                                                                                res=T.STRING})
                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "concat",   FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[false, false]},
                                                                                label=newlabel,
                                                                                params=[T.STRING, T.STRING],
                                                                                res=T.STRING})
                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "not",      FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[false]},
                                                                               label=newlabel,
                                                                               params=[T.INT],
                                                                               res=T.INT})
                val newlabel = Temp.newlabel()
                val venv = Symbol.enter(venv, Symbol.symbol "exit",     FunEnt{level=Translate.newLevel{parent=Translate.outermost,
                                                                                                        name=newlabel,
                                                                                                        formals=[false]},
                                                                               label=newlabel,
                                                                               params=[T.INT],
                                                                               res=T.UNIT})
        in
                (* find escaping variables *)
                (*FE.findEscape(exp); *)

                print "===========================================\n";
                print "AST\n";
                PrintAbsyn.print(TextIO.stdOut, exp);
                print "===========================================\n\n";

                (* recurse *)
                let val {exp=expTree, ty=_} = transExp(tenv, venv, exp, Translate.outermost, NONE)
                in  
                    
                    (*Translate.printTree(expTree);*)
                    Translate.procEntryExit{level=Translate.outermost,
                                            bodyExp=expTree}
                end;

                (* return frag list *)
                Translate.getResult()
        end)
end
