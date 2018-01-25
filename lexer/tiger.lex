type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

val legal_eof = ref true;

fun eof() = let val pos = hd(!linePos)
              in
                ( if !legal_eof then ()
                  else (ErrorMsg.error (hd(!linePos)) "open string or comment")
                );
                Tokens.EOF(!lineNum, hd(!linePos))
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
%s COMMENT STRING ESC;

digits=[0-9]+;
digit=[0-9];
ws=[\ \t]+;
wss=[\ \t\n\f];
letter=[a-zA-Z];
sym= "," | ":" | ";" | "(" | ")" | "[" | "]" | "{" | "}" | "." | "+" | "-" | "*" | "/" | "=" | "<>" | "<" | ">" | "<=" | ">=" | "&" | "|" | ":=" ;
esc_char = n | t | \" | \\ | "^C" | "^Z";

keywords = "int" | "string" | "function" | "break" | "of" | "end" | "in" | "nil" | "let" | "do" | "to" | "for" | "while" | "else" | "then" | "if" | "array" ; 

%%

<INITIAL>{keywords}       =>(case yytext of
          "int"           => Tokens.TYPE_INT(!lineNum, (yypos - hd(!linePos)))
          | "string"      => Tokens.TYPE_STR(!lineNum, (yypos - hd(!linePos)))
			    |"function"     => Tokens.FUNCTION(!lineNum,(yypos - hd(!linePos)))
          | "break"       => Tokens.BREAK(!lineNum,(yypos - hd(!linePos)))
			    | "of"          => Tokens.OF(!lineNum,(yypos - hd(!linePos)))
			    | "end"         => Tokens.END(!lineNum,(yypos - hd(!linePos)))
          | "in"          => Tokens.IN(!lineNum,(yypos - hd(!linePos)))
			    | "nil"         => Tokens.NIL(!lineNum,(yypos - hd(!linePos)))
          | "let"         => Tokens.LET(!lineNum,(yypos - hd(!linePos)))
			    | "do"          => Tokens.DO(!lineNum,(yypos - hd(!linePos)))
			    | "to"          => Tokens.TO(!lineNum,(yypos - hd(!linePos)))
			    | "for"         => Tokens.FOR(!lineNum,(yypos - hd(!linePos)))
			    | "while"       => Tokens.WHILE(!lineNum,(yypos - hd(!linePos)))
			    | "else"        => Tokens.ELSE(!lineNum,(yypos - hd(!linePos)))
			    | "then"        => Tokens.THEN(!lineNum,(yypos - hd(!linePos)))
			    | "if"          => Tokens.IF(!lineNum,(yypos - hd(!linePos)))
			    | "array"       => Tokens.ARRAY(!lineNum,(yypos - hd(!linePos)))
                              );

<INITIAL>var  	         => (Tokens.VAR(!lineNum,(yypos - hd(!linePos))));
<INITIAL>type            =>  (Tokens.TYPE(!lineNum,(yypos - hd(!linePos))));
<INITIAL>{sym}           =>  (case yytext of
				"," => Tokens.COMMA(!lineNum,(yypos - hd(!linePos)))
				| ":" => Tokens.COLON(!lineNum,(yypos - hd(!linePos)))
                                | ";" => Tokens.SEMICOLON(!lineNum,(yypos - hd(!linePos)))
				| "(" => Tokens.LPAREN(!lineNum,(yypos - hd(!linePos)))
				| ")" => Tokens.RPAREN(!lineNum,(yypos - hd(!linePos)))
				| "[" => Tokens.LBRACK(!lineNum,(yypos - hd(!linePos)))
				| "]" => Tokens.RBRACK(!lineNum,(yypos - hd(!linePos)))
				| "{" => Tokens.LBRACE(!lineNum,(yypos - hd(!linePos)))
				| "}" => Tokens.RBRACE(!lineNum,(yypos - hd(!linePos)))
				| "." => Tokens.DOT(!lineNum,(yypos - hd(!linePos)))
				| "+" => Tokens.PLUS(!lineNum,(yypos - hd(!linePos)))
				| "-" => Tokens.MINUS(!lineNum,(yypos - hd(!linePos)))
				| "*" => Tokens.TIMES(!lineNum,(yypos - hd(!linePos)))
				| "/" => Tokens.DIVIDE(!lineNum,(yypos - hd(!linePos)))
				| "=" => Tokens.EQ(!lineNum,(yypos - hd(!linePos)))
				| "<>" => Tokens.NEQ(!lineNum,(yypos - hd(!linePos)))
				| "<" => Tokens.LT(!lineNum,(yypos - hd(!linePos)))
				| ">" => Tokens.GT(!lineNum,(yypos - hd(!linePos)))
				| "<=" => Tokens.LE(!lineNum,(yypos - hd(!linePos)))
				| ">=" => Tokens.GE(!lineNum,(yypos - hd(!linePos))) 
				| "&" => Tokens.AND(!lineNum,(yypos - hd(!linePos)))
				| "|" => Tokens.OR(!lineNum,(yypos - hd(!linePos)))
				| ":=" => Tokens.ASSIGN(!lineNum,(yypos - hd(!linePos))));

<INITIAL>{letter}({digits}|{letter}|_)*   => (Tokens.ID(yytext, !lineNum,(yypos - hd(!linePos))));
<INITIAL>{ws}       => (continue());
<INITIAL>\n	        => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>{digits}   => (case Int.fromString(yytext) of
                          SOME i => (Tokens.INT(i, !lineNum,(yypos - hd(!linePos)))));
<INITIAL>"/*"       => (YYBEGIN COMMENT; legal_eof := false; comlevel := !comlevel+1; continue());
<INITIAL>\"         => (YYBEGIN STRING; legal_eof := false; continue());

<COMMENT>"/*"       => (comlevel := !comlevel+1; continue());
<COMMENT>"*/"       => (comlevel := !comlevel-1; if !comlevel = 0
                          then (YYBEGIN INITIAL; legal_eof := true; continue())
                          else continue());
<COMMENT>\n	        => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<COMMENT>.          => (continue());

<STRING>\"	        => (strtmp := !strtok; strtok := ""; YYBEGIN INITIAL; legal_eof := true; Tokens.STRING(!strtmp, !lineNum,(yypos - hd(!linePos))));
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

