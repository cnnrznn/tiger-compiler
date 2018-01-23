structure Mlex  = struct

    structure yyInput : sig

        type stream
	val mkStream : (int -> string) -> stream
	val fromStream : TextIO.StreamIO.instream -> stream
	val getc : stream -> (Char.char * stream) option
	val getpos : stream -> int
	val getlineNo : stream -> int
	val subtract : stream * stream -> string
	val eof : stream -> bool
	val lastWasNL : stream -> bool

      end = struct

        structure TIO = TextIO
        structure TSIO = TIO.StreamIO
	structure TPIO = TextPrimIO

        datatype stream = Stream of {
            strm : TSIO.instream,
	    id : int,  (* track which streams originated 
			* from the same stream *)
	    pos : int,
	    lineNo : int,
	    lastWasNL : bool
          }

	local
	  val next = ref 0
	in
	fun nextId() = !next before (next := !next + 1)
	end

	val initPos = 2 (* ml-lex bug compatibility *)

	fun mkStream inputN = let
              val strm = TSIO.mkInstream 
			   (TPIO.RD {
			        name = "lexgen",
				chunkSize = 4096,
				readVec = SOME inputN,
				readArr = NONE,
				readVecNB = NONE,
				readArrNB = NONE,
				block = NONE,
				canInput = NONE,
				avail = (fn () => NONE),
				getPos = NONE,
				setPos = NONE,
				endPos = NONE,
				verifyPos = NONE,
				close = (fn () => ()),
				ioDesc = NONE
			      }, "")
	      in 
		Stream {strm = strm, id = nextId(), pos = initPos, lineNo = 1,
			lastWasNL = true}
	      end

	fun fromStream strm = Stream {
		strm = strm, id = nextId(), pos = initPos, lineNo = 1, lastWasNL = true
	      }

	fun getc (Stream {strm, pos, id, lineNo, ...}) = (case TSIO.input1 strm
              of NONE => NONE
	       | SOME (c, strm') => 
		   SOME (c, Stream {
			        strm = strm', 
				pos = pos+1, 
				id = id,
				lineNo = lineNo + 
					 (if c = #"\n" then 1 else 0),
				lastWasNL = (c = #"\n")
			      })
	     (* end case*))

	fun getpos (Stream {pos, ...}) = pos

	fun getlineNo (Stream {lineNo, ...}) = lineNo

	fun subtract (new, old) = let
	      val Stream {strm = strm, pos = oldPos, id = oldId, ...} = old
	      val Stream {pos = newPos, id = newId, ...} = new
              val (diff, _) = if newId = oldId andalso newPos >= oldPos
			      then TSIO.inputN (strm, newPos - oldPos)
			      else raise Fail 
				"BUG: yyInput: attempted to subtract incompatible streams"
	      in 
		diff 
	      end

	fun eof s = not (isSome (getc s))

	fun lastWasNL (Stream {lastWasNL, ...}) = lastWasNL

      end

    datatype yystart_state = 
ESC | STRING | COMMENT | INITIAL
    structure UserDeclarations = 
      struct

type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end

val comlevel = ref 0;

val strtok = ref "";
val strtmp = ref "";




      end

    datatype yymatch 
      = yyNO_MATCH
      | yyMATCH of yyInput.stream * action * yymatch
    withtype action = yyInput.stream * yymatch -> UserDeclarations.lexresult

    local

    val yytable = 
Vector.fromList []
    fun mk yyins = let
        (* current start state *)
        val yyss = ref INITIAL
	fun YYBEGIN ss = (yyss := ss)
	(* current input stream *)
        val yystrm = ref yyins
	(* get one char of input *)
	val yygetc = yyInput.getc
	(* create yytext *)
	fun yymktext(strm) = yyInput.subtract (strm, !yystrm)
        open UserDeclarations
        fun lex 
(yyarg as ()) = let 
     fun continue() = let
            val yylastwasn = yyInput.lastWasNL (!yystrm)
            fun yystuck (yyNO_MATCH) = raise Fail "stuck state"
	      | yystuck (yyMATCH (strm, action, old)) = 
		  action (strm, old)
	    val yypos = yyInput.getpos (!yystrm)
	    val yygetlineNo = yyInput.getlineNo
	    fun yyactsToMatches (strm, [],	  oldMatches) = oldMatches
	      | yyactsToMatches (strm, act::acts, oldMatches) = 
		  yyMATCH (strm, act, yyactsToMatches (strm, acts, oldMatches))
	    fun yygo actTable = 
		(fn (~1, _, oldMatches) => yystuck oldMatches
		  | (curState, strm, oldMatches) => let
		      val (transitions, finals') = Vector.sub (yytable, curState)
		      val finals = List.map (fn i => Vector.sub (actTable, i)) finals'
		      fun tryfinal() = 
		            yystuck (yyactsToMatches (strm, finals, oldMatches))
		      fun find (c, []) = NONE
			| find (c, (c1, c2, s)::ts) = 
		            if c1 <= c andalso c <= c2 then SOME s
			    else find (c, ts)
		      in case yygetc strm
			  of SOME(c, strm') => 
			       (case find (c, transitions)
				 of NONE => tryfinal()
				  | SOME n => 
				      yygo actTable
					(n, strm', 
					 yyactsToMatches (strm, finals, oldMatches)))
			   | NONE => tryfinal()
		      end)
	    in 
let
fun yyAction0 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.VAR(yypos,yypos+3)))
fun yyAction1 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.TYPE(yypos,yypos)))
fun yyAction2 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (case yytext of
				"," => Tokens.COMMA(yypos,yypos+1)
				| ":" => Tokens.COLON(yypos,yypos+1)
                                | ";" => Tokens.SEMICOLON(yypos,yypos+1)
				| "(" => Tokens.LPAREN(yypos,yypos+1)
				| ")" => Tokens.RPAREN(yypos,yypos+1)
				| "[" => Tokens.LBRACK(yypos,yypos+1)
				| "]" => Tokens.RBRACK(yypos,yypos+1)
				| "{" => Tokens.LBRACE(yypos,yypos+1)
				| "}" => Tokens.RBRACE(yypos,yypos+1)
				| "." => Tokens.DOT(yypos,yypos+1)
				| "+" => Tokens.PLUS(yypos,yypos+1)
				| "-" => Tokens.MINUS(yypos,yypos+1)
				| "*" => Tokens.TIMES(yypos,yypos+1)
				| "/" => Tokens.DIVIDE(yypos,yypos+1)
				| "=" => Tokens.EQ(yypos,yypos+1)
				| "<>" => Tokens.NEQ(yypos,yypos+2)
				| "<" => Tokens.LT(yypos,yypos+1)
				| ">" => Tokens.GT(yypos,yypos+1)
				| "<=" => Tokens.LE(yypos,yypos+2)
				| ">=" => Tokens.GE(yypos,yypos+2) 
				| "&" => Tokens.AND(yypos,yypos+1)
				| "|" => Tokens.OR(yypos,yypos+1)
				| ":=" => Tokens.ASSIGN(yypos,yypos+2))
      end
fun yyAction3 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction4 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.ID(yytext, yypos, yypos))
      end
fun yyAction5 (strm, lastMatch : yymatch) = (yystrm := strm;
      (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue()))
fun yyAction6 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (case Int.fromString(yytext) of
                      SOME i => (Tokens.INT(i, yypos, yypos)))
      end
fun yyAction7 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN COMMENT; comlevel := !comlevel+1; continue()))
fun yyAction8 (strm, lastMatch : yymatch) = (yystrm := strm;
      (comlevel := !comlevel+1; continue()))
fun yyAction9 (strm, lastMatch : yymatch) = (yystrm := strm;
      (comlevel := !comlevel-1; if !comlevel = 0
                                                      then (YYBEGIN INITIAL; continue())
                                                      else continue()))
fun yyAction10 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction11 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN STRING; continue()))
fun yyAction12 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN ESC; continue()))
fun yyAction13 (strm, lastMatch : yymatch) = (yystrm := strm;
      (strtmp := !strtok; strtok := ""; YYBEGIN INITIAL; Tokens.STRING(!strtmp, yypos, yypos)))
fun yyAction14 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (strtok := !strtok ^ yytext; continue())
      end
fun yyAction15 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (strtok := !strtok ^ "\\" ^ yytext; YYBEGIN STRING; continue())
      end
fun yyAction16 (strm, lastMatch : yymatch) = (yystrm := strm;
      (print "illegal use in string literal"; continue()))
fun yyAction17 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (ErrorMsg.error yypos ("illegal character " ^ yytext); continue())
      end
fun yyQ27 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction4(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp = #":"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction4(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction4(strm, yyNO_MATCH)
                  else yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp = #"`"
              then yyAction4(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"_"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
and yyQ26 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction4(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp = #":"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction4(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction4(strm, yyNO_MATCH)
                  else yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp = #"`"
              then yyAction4(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"_"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ29 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction0(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction0(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp = #":"
                  then yyAction0(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction0(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction0(strm, yyNO_MATCH)
                  else yyQ27(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp = #"`"
              then yyAction0(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"_"
                  then yyQ27(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                  else yyAction0(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
              else yyAction0(strm, yyNO_MATCH)
      (* end case *))
fun yyQ28 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction4(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp = #"r"
              then yyQ29(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"r"
              then if inp = #"`"
                  then yyAction4(strm, yyNO_MATCH)
                  else yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp <= #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ25 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction4(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp = #"b"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"b"
              then if inp = #"`"
                  then yyAction4(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp <= #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ32 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction1(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction1(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp = #":"
                  then yyAction1(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction1(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction1(strm, yyNO_MATCH)
                  else yyQ27(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
            else if inp = #"`"
              then yyAction1(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"_"
                  then yyQ27(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
                  else yyAction1(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
              else yyAction1(strm, yyNO_MATCH)
      (* end case *))
fun yyQ31 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction4(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp = #"e"
              then yyQ32(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"e"
              then if inp = #"`"
                  then yyAction4(strm, yyNO_MATCH)
                  else yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp <= #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ30 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction4(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp = #"p"
              then yyQ31(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"p"
              then if inp = #"`"
                  then yyAction4(strm, yyNO_MATCH)
                  else yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp <= #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ24 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction4(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp = #"y"
              then yyQ30(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"y"
              then if inp = #"`"
                  then yyAction4(strm, yyNO_MATCH)
                  else yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp = #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ23 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction4(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp = #":"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction4(strm, yyNO_MATCH)
                      else yyQ26(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction4(strm, yyNO_MATCH)
                  else yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp = #"`"
              then yyAction4(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"_"
                  then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ27(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ33 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ22 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"="
              then yyQ33(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
            else if inp < #"="
              then yyAction2(strm, yyNO_MATCH)
            else if inp <= #">"
              then yyQ33(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
              else yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ21 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"="
              then yyQ33(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
              else yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ34 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction6(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ34(strm', yyMATCH(strm, yyAction6, yyNO_MATCH))
            else if inp < #"0"
              then yyAction6(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ34(strm', yyMATCH(strm, yyAction6, yyNO_MATCH))
              else yyAction6(strm, yyNO_MATCH)
      (* end case *))
fun yyQ20 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction6(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ34(strm', yyMATCH(strm, yyAction6, yyNO_MATCH))
            else if inp < #"0"
              then yyAction6(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ34(strm', yyMATCH(strm, yyAction6, yyNO_MATCH))
              else yyAction6(strm, yyNO_MATCH)
      (* end case *))
fun yyQ35 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction7(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction7(strm, yyNO_MATCH)
      (* end case *))
fun yyQ19 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ35(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
              else yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ18 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ17 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction11(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction11(strm, yyNO_MATCH)
      (* end case *))
fun yyQ16 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction5(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction5(strm, yyNO_MATCH)
      (* end case *))
fun yyQ36 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction3(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyAction3(strm, yyNO_MATCH)
            else if inp < #"\n"
              then if inp = #"\t"
                  then yyQ36(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                  else yyAction3(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ36(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
              else yyAction3(strm, yyNO_MATCH)
      (* end case *))
fun yyQ15 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction3(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyAction3(strm, yyNO_MATCH)
            else if inp < #"\n"
              then if inp = #"\t"
                  then yyQ36(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                  else yyAction3(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ36(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
              else yyAction3(strm, yyNO_MATCH)
      (* end case *))
fun yyQ14 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ3 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"<"
              then yyQ22(strm', lastMatch)
            else if inp < #"<"
              then if inp = #"#"
                  then yyQ14(strm', lastMatch)
                else if inp < #"#"
                  then if inp = #"\v"
                      then yyQ14(strm', lastMatch)
                    else if inp < #"\v"
                      then if inp = #"\t"
                          then yyQ15(strm', lastMatch)
                        else if inp = #"\n"
                          then yyQ16(strm', lastMatch)
                          else yyQ14(strm', lastMatch)
                    else if inp = #"!"
                      then yyQ14(strm', lastMatch)
                    else if inp < #"!"
                      then if inp = #" "
                          then yyQ15(strm', lastMatch)
                          else yyQ14(strm', lastMatch)
                      else yyQ17(strm', lastMatch)
                else if inp = #"/"
                  then yyQ19(strm', lastMatch)
                else if inp < #"/"
                  then if inp = #"'"
                      then yyQ14(strm', lastMatch)
                    else if inp < #"'"
                      then if inp = #"&"
                          then yyQ18(strm', lastMatch)
                          else yyQ14(strm', lastMatch)
                      else yyQ18(strm', lastMatch)
                else if inp = #":"
                  then yyQ21(strm', lastMatch)
                else if inp = #";"
                  then yyQ18(strm', lastMatch)
                  else yyQ20(strm', lastMatch)
            else if inp = #"^"
              then yyQ14(strm', lastMatch)
            else if inp < #"^"
              then if inp = #"A"
                  then yyQ23(strm', lastMatch)
                else if inp < #"A"
                  then if inp = #">"
                      then yyQ21(strm', lastMatch)
                    else if inp = #"="
                      then yyQ18(strm', lastMatch)
                      else yyQ14(strm', lastMatch)
                else if inp = #"\\"
                  then yyQ14(strm', lastMatch)
                else if inp < #"\\"
                  then if inp = #"["
                      then yyQ18(strm', lastMatch)
                      else yyQ23(strm', lastMatch)
                  else yyQ18(strm', lastMatch)
            else if inp = #"v"
              then yyQ25(strm', lastMatch)
            else if inp < #"v"
              then if inp = #"t"
                  then yyQ24(strm', lastMatch)
                else if inp < #"t"
                  then if inp <= #"`"
                      then yyQ14(strm', lastMatch)
                      else yyQ23(strm', lastMatch)
                  else yyQ23(strm', lastMatch)
            else if inp = #"{"
              then yyQ18(strm', lastMatch)
            else if inp < #"{"
              then yyQ23(strm', lastMatch)
            else if inp <= #"}"
              then yyQ18(strm', lastMatch)
              else yyQ14(strm', lastMatch)
      (* end case *))
fun yyQ12 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction8(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction8(strm, yyNO_MATCH)
      (* end case *))
fun yyQ11 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction10(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ12(strm', yyMATCH(strm, yyAction10, yyNO_MATCH))
              else yyAction10(strm, yyNO_MATCH)
      (* end case *))
fun yyQ13 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction9(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction9(strm, yyNO_MATCH)
      (* end case *))
fun yyQ10 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction10(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ13(strm', yyMATCH(strm, yyAction10, yyNO_MATCH))
              else yyAction10(strm, yyNO_MATCH)
      (* end case *))
fun yyQ9 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction10(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction10(strm, yyNO_MATCH)
      (* end case *))
fun yyQ2 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ10(strm', lastMatch)
            else if inp < #"*"
              then if inp = #"\n"
                  then if yyInput.eof(!(yystrm))
                      then UserDeclarations.eof(yyarg)
                      else yystuck(lastMatch)
                  else yyQ9(strm', lastMatch)
            else if inp = #"/"
              then yyQ11(strm', lastMatch)
              else yyQ9(strm', lastMatch)
      (* end case *))
fun yyQ8 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction12(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction12(strm, yyNO_MATCH)
      (* end case *))
fun yyQ7 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction13(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction13(strm, yyNO_MATCH)
      (* end case *))
fun yyQ6 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction14(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction14(strm, yyNO_MATCH)
      (* end case *))
fun yyQ1 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"\""
              then yyQ7(strm', lastMatch)
            else if inp < #"\""
              then if inp = #"\n"
                  then if yyInput.eof(!(yystrm))
                      then UserDeclarations.eof(yyarg)
                      else yystuck(lastMatch)
                  else yyQ6(strm', lastMatch)
            else if inp = #"\\"
              then yyQ8(strm', lastMatch)
              else yyQ6(strm', lastMatch)
      (* end case *))
fun yyQ5 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction15(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction15(strm, yyNO_MATCH)
      (* end case *))
fun yyQ4 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction16(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction16(strm, yyNO_MATCH)
      (* end case *))
fun yyQ0 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"n"
              then yyQ5(strm', lastMatch)
            else if inp < #"n"
              then if inp = #"\n"
                  then if yyInput.eof(!(yystrm))
                      then UserDeclarations.eof(yyarg)
                      else yystuck(lastMatch)
                  else yyQ4(strm', lastMatch)
            else if inp = #"t"
              then yyQ5(strm', lastMatch)
              else yyQ4(strm', lastMatch)
      (* end case *))
in
  (case (!(yyss))
   of ESC => yyQ0(!(yystrm), yyNO_MATCH)
    | STRING => yyQ1(!(yystrm), yyNO_MATCH)
    | COMMENT => yyQ2(!(yystrm), yyNO_MATCH)
    | INITIAL => yyQ3(!(yystrm), yyNO_MATCH)
  (* end case *))
end
            end
	  in 
            continue() 	  
	    handle IO.Io{cause, ...} => raise cause
          end
        in 
          lex 
        end
    in
    fun makeLexer yyinputN = mk (yyInput.mkStream yyinputN)
    end

  end
