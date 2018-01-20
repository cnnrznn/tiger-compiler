type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end

val comlevel = ref 0;


%% 
%s COMMENT;

digits=[0-9]+;
ws=[\ \t]+;
letter=[a-zA-Z];
%%
<INITIAL>var  	          => (Tokens.VAR(yypos,yypos+3));
<INITIAL>type            => (Tokens.TYPE(yypos,yypos));

<INITIAL>{ws}             => (continue());
<INITIAL>{letter}({digits}|{letter}|_)* => (Tokens.ID(yytext, yypos, yypos));
<INITIAL>\n	            => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>","	            => (Tokens.COMMA(yypos,yypos+1));
<INITIAL>[+-]?{digits}   => (case Int.fromString(yytext) of
                      SOME i => (Tokens.INT(i, yypos, yypos)));
<INITIAL>"/*"            => (YYBEGIN COMMENT; comlevel := !comlevel+1; continue());
<COMMENT>"/*"            => (comlevel := !comlevel+1; continue());
<COMMENT>"*/"            => (comlevel := !comlevel-1; if !comlevel = 0
                                                      then (YYBEGIN INITIAL; continue())
                                                      else continue());
<COMMENT>.  => (continue());
.               => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());

