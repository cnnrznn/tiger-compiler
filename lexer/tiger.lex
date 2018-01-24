type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end

val comlevel = ref 0;

val strtok = ref "";
val strtmp = ref "";


%% 
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
			     "function" => Tokens.FUNCTION(yypos, yypos+8)
                             | "break"  => Tokens.BREAK(yypos, yypos+5)
			     | "of"     => Tokens.OF(yypos, yypos+2)
			     | "end"    => Tokens.END(yypos, yypos+3)
                             | "in"     => Tokens.IN(yypos, yypos+2)
			     | "nil"    => Tokens.NIL(yypos, yypos+3)	
                             | "let"    => Tokens.LET(yypos, yypos+3)
			     | "do"     => Tokens.DO(yypos, yypos+2)
			     | "to"     => Tokens.TO(yypos, yypos+2)
			     | "for"    => Tokens.FOR(yypos, yypos+3)
			     | "while"  => Tokens.WHILE(yypos, yypos+5)
			     | "else"   => Tokens.ELSE(yypos, yypos+4)
			     | "then"   => Tokens.THEN(yypos, yypos+4)
			     | "if"     => Tokens.IF(yypos, yypos+2)
			     | "array"  => Tokens.ARRAY(yypos, yypos+5)
                              );

<INITIAL>var  	         => (Tokens.VAR(yypos,yypos+3));
<INITIAL>type            =>  (Tokens.TYPE(yypos,yypos));
<INITIAL>{sym}           =>  (case yytext of
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
				| ":=" => Tokens.ASSIGN(yypos,yypos+2));

<INITIAL>{ws}             => (continue());
<INITIAL>{letter}({digits}|{letter}|_)* => (Tokens.ID(yytext, yypos, yypos));
<INITIAL>\n	            => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>{digits}   => (case Int.fromString(yytext) of
                      SOME i => (Tokens.INT(i, yypos, yypos)));
<INITIAL>"/*"            => (YYBEGIN COMMENT; comlevel := !comlevel+1; continue());
<COMMENT>"/*"            => (comlevel := !comlevel+1; continue());
<COMMENT>"*/"            => (comlevel := !comlevel-1; if !comlevel = 0
                                                      then (YYBEGIN INITIAL; continue())
                                                      else continue());
<COMMENT>.               => (continue());

<INITIAL>\"              => (YYBEGIN STRING; continue());
<STRING>\\ 	         => (YYBEGIN ESC; continue());
<STRING>\"	         => (strtmp := !strtok; strtok := ""; YYBEGIN INITIAL; Tokens.STRING(!strtmp, yypos, yypos));
<STRING>.	         => (strtok := !strtok ^ yytext; continue());

<ESC>{wss}+\\      => (YYBEGIN STRING; continue());
<ESC>{digit}{digit}{digit} => (case Int.fromString(yytext) of
                                SOME i => ( if i < 128 then
                                              (strtok := !strtok ^ (Char.toString(chr(i))); YYBEGIN STRING; continue())
                                            else
                                              (ErrorMsg.error yypos ("invalid ASCII \\" ^ yytext); continue())
                                          )
                                );
<ESC>{esc_char}          => (strtok := !strtok ^ "\\" ^ yytext; YYBEGIN STRING; continue());
<ESC>.                   => (ErrorMsg.error yypos ("illegal use in string literal " ^ yytext); continue());

.           => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());

