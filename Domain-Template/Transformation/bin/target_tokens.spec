datatype lexresult	= SHELL of string * string * {line: word, column: word};
val error 			= fn x => TextIO.output(TextIO.stdOut,x ^ "\n")
val eof 			= fn () => SHELL("","eof",getNextTokenPos(""))
(* ============================================================================================== *)
(* ------------------------------------------------------------------ *)
(* assumes that ">" does not occur as part of a nonterminal symbol *)
fun generateSchemaTokenName( yytext ) =
    let
        fun split(x, []   ) =  raise General.Fail("an_error")
          | split(x, y::ys) = if x=y then ys else split(x,ys);
                                                    
        fun splitFirst(symbol,[])    = 	[] (* symbol was not in the input list *)
          | splitFirst(symbol,x::xs) = 	if x = symbol 
                        then (* found split point *)
                            []
                        else (* keep looking      *)
                            x::splitFirst(symbol,xs);
                                                                        
        val s0   = explode(yytext);
        val s1   = split(#"<",s0);
        val s2   = splitFirst(#">",s1);  
    in
        implode(explode("!#schema_variable_") @ s2)        
    end;
    
(* ------------------------------------------------------------------ *)

(* ============================================================================================== *)
%%
%header (functor Target_LexFn(val getNextTokenPos : string -> {line: word, column: word}));

digit        = [0-9];
posDigit     = [1-9]; 
integer      = 0 | {posDigit}{digit}*;

alpha        = [A-Za-z];
alphanumeric = [A-Za-z0-9_];
identifier   = {alpha}{alphanumeric}*; 

boolean 	 = "true" | "false"; 

ws           = [\  \t \n];

schema_id    = "<" {alpha}{alphanumeric}* ">_" {alphanumeric}+;
comment      = "//" .* ;

%%
{ws}+        => ( getNextTokenPos(yytext); lex()  );
{comment}    => ( getNextTokenPos(yytext); lex()  );

{digit}+                      => ( SHELL("integer"   , yytext,     getNextTokenPos(yytext))    );
{alpha}{alphanumeric}*        => ( SHELL("id"        , yytext,     getNextTokenPos(yytext))    );



{schema_id}                   => ( SHELL(generateSchemaTokenName(yytext), yytext, getNextTokenPos(yytext))    );
"[:]"                         => ( SHELL("" , yytext, getNextTokenPos(yytext))    );

 .                            => ( error("ignored an unprintable character: " ^ yytext); getNextTokenPos(yytext); lex()  );
