type pos = int
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue,pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

val legal_eof = ref true;

fun eof() = let val pos = hd(!linePos)
              in
                ( if !legal_eof then ()
                  else (ErrorMsg.error (pos) "open string or comment")
                );
                Tokens.EOF(pos, pos)
              end
                

val comlevel = ref 0;

val strtok = ref "";
val strtmp = ref "";

fun update_pos(str:string, start:int, off:int):unit =
  let
    val c = String.sub(str, off);
  in
    (if Char.toString c = "\\n" then
      (lineNum := !lineNum+1; linePos := start+off :: !linePos)
    else ());
    (if off+1 < String.size str then update_pos(str, start, off+1)
    else ())
  end

%% 
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));

%s COMMENT STRING ESC;

digits=[0-9]+;
digit=[0-9];
ws=[\ \t]+;
wss=[\ \t\n\f];
letter=[a-zA-Z];
sym= "," | ":" | ";" | "(" | ")" | "[" | "]" | "{" | "}" | "." | "+" | "-" | "*" | "/" | "=" | "<>" | "<" | ">" | "<=" | ">=" | "&" | "|" | ":=" ;
esc_char = n | t | \" | \\ | "^C" | "^Z";

keywords = "function" | "break" | "of" | "end" | "in" | "nil" | "let" | "do" | "to" | "for" | "while" | "else" | "then" | "if" | "array" ; 

%%

<INITIAL>{keywords}       =>(case yytext of
        "function"     => Tokens.FUNCTION(yypos, yypos)
          | "break"       => Tokens.BREAK(yypos, yypos)
			    | "of"          => Tokens.OF(yypos, yypos)
			    | "end"         => Tokens.END(yypos, yypos)
          | "in"          => Tokens.IN(yypos, yypos)
			    | "nil"         => Tokens.NIL(yypos, yypos)
          | "let"         => Tokens.LET(yypos, yypos)
			    | "do"          => Tokens.DO(yypos, yypos)
			    | "to"          => Tokens.TO(yypos, yypos)
			    | "for"         => Tokens.FOR(yypos, yypos)
			    | "while"       => Tokens.WHILE(yypos, yypos)
			    | "else"        => Tokens.ELSE(yypos, yypos)
			    | "then"        => Tokens.THEN(yypos, yypos)
			    | "if"          => Tokens.IF(yypos, yypos)
			    | "array"       => Tokens.ARRAY(yypos, yypos)
                              );

<INITIAL>var  	         => (Tokens.VAR(yypos, yypos));
<INITIAL>type            =>  (Tokens.TYPE(yypos, yypos));
<INITIAL>{sym}           =>  (case yytext of
				"," => Tokens.COMMA(yypos, yypos)
				| ":" => Tokens.COLON(yypos, yypos)
                                | ";" => Tokens.SEMICOLON(yypos, yypos)
				| "(" => Tokens.LPAREN(yypos, yypos)
				| ")" => Tokens.RPAREN(yypos, yypos)
				| "[" => Tokens.LBRACK(yypos, yypos)
				| "]" => Tokens.RBRACK(yypos, yypos)
				| "{" => Tokens.LBRACE(yypos, yypos)
				| "}" => Tokens.RBRACE(yypos, yypos)
				| "." => Tokens.DOT(yypos, yypos)
				| "+" => Tokens.PLUS(yypos, yypos)
				| "-" => Tokens.MINUS(yypos, yypos)
				| "*" => Tokens.TIMES(yypos, yypos)
				| "/" => Tokens.DIVIDE(yypos, yypos)
				| "=" => Tokens.EQ(yypos, yypos)
				| "<>" => Tokens.NEQ(yypos, yypos)
				| "<" => Tokens.LT(yypos, yypos)
				| ">" => Tokens.GT(yypos, yypos)
				| "<=" => Tokens.LE(yypos, yypos)
				| ">=" => Tokens.GE(yypos, yypos) 
				| "&" => Tokens.AND(yypos, yypos)
				| "|" => Tokens.OR(yypos, yypos)
				| ":=" => Tokens.ASSIGN(yypos, yypos));

<INITIAL>{letter}({digits}|{letter}|_)*   => (Tokens.ID(yytext, yypos, yypos));
<INITIAL>{ws}       => (continue());
<INITIAL>\n	        => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>{digits}   => (case Int.fromString(yytext) of
                          SOME i => (Tokens.INT(i, yypos, yypos)));
<INITIAL>"/*"       => (YYBEGIN COMMENT; legal_eof := false; comlevel := !comlevel+1; continue());
<INITIAL>\"         => (YYBEGIN STRING; legal_eof := false; continue());

<COMMENT>"/*"       => (comlevel := !comlevel+1; continue());
<COMMENT>"*/"       => (comlevel := !comlevel-1; if !comlevel = 0
                          then (YYBEGIN INITIAL; legal_eof := true; continue())
                          else continue());
<COMMENT>\n	        => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<COMMENT>.          => (continue());

<STRING>\"	        => (strtmp := !strtok; strtok := ""; YYBEGIN INITIAL; legal_eof := true; Tokens.STRING(!strtmp, yypos, yypos));
<STRING>\n          => (lineNum := !lineNum+1; linePos := yypos :: !linePos; ErrorMsg.error yypos ("line break needed in string"); continue());
<STRING>\\ 	        => (YYBEGIN ESC; continue());
<STRING>.	          => (strtok := !strtok ^ yytext; continue());

<ESC>{wss}+         => (YYBEGIN STRING;
                        ErrorMsg.error (yypos-1) ("unclosed line break");
                        update_pos(yytext, yypos, 0);
                        continue());
<ESC>{wss}+\\       => (YYBEGIN STRING;
                        update_pos(yytext, yypos, 0);
                        continue());
<ESC>{digit}{digit}{digit} => (case Int.fromString(yytext) of
                                SOME i => ( YYBEGIN STRING;
                                            strtok := !strtok ^ (Char.toString(chr(i)));
                                            if i < 128 then
                                              ()
                                            else
                                              (ErrorMsg.error yypos ("invalid ASCII \\" ^ yytext))
                                            ;
                                            continue()
                                          )
                              );
<ESC>{esc_char}     => (strtok := !strtok ^ "\\" ^ yytext; YYBEGIN STRING; continue());
<ESC>.              => (ErrorMsg.error yypos ("illegal use in string literal " ^ yytext); continue());

.           => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());

