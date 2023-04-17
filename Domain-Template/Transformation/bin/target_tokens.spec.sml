(*#line 30.10 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec"*)functor Target_LexFn(val getNextTokenPos : string -> {line: word, column: word})(*#line 1.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec.sml"*)
=
   struct
    structure UserDeclarations =
      struct
(*#line 1.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec"*)datatype lexresult	= SHELL of string * string * {line: word, column: word};
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
(*#line 34.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec.sml"*)
end (* end of user routines *)
exception LexError (* raised if illegal leaf action tried *)
structure Internal =
	struct

datatype yyfinstate = N of int
type statedata = {fin : yyfinstate list, trans: string}
(* transition & final state table *)
val tab = let
val s = [ 
 (0, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (1, 
"\003\003\003\003\003\003\003\003\003\018\019\003\003\003\003\003\
\\003\003\003\003\003\003\003\003\003\003\003\003\003\003\003\003\
\\018\003\003\003\003\003\003\003\003\003\003\003\003\003\003\016\
\\014\014\014\014\014\014\014\014\014\014\003\003\009\003\003\003\
\\003\004\004\004\004\004\004\004\004\004\004\004\004\004\004\004\
\\004\004\004\004\004\004\004\004\004\004\004\006\003\003\003\003\
\\003\004\004\004\004\004\004\004\004\004\004\004\004\004\004\004\
\\004\004\004\004\004\004\004\004\004\004\004\003\003\003\003\003\
\\003"
),
 (4, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\005\005\005\005\005\005\005\005\005\005\000\000\000\000\000\000\
\\000\005\005\005\005\005\005\005\005\005\005\005\005\005\005\005\
\\005\005\005\005\005\005\005\005\005\005\005\000\000\000\000\005\
\\000\005\005\005\005\005\005\005\005\005\005\005\005\005\005\005\
\\005\005\005\005\005\005\005\005\005\005\005\000\000\000\000\000\
\\000"
),
 (6, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\007\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (7, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\008\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (9, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\000\000\000\000\
\\000\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\000\000\000\000\
\\000"
),
 (10, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\010\010\010\010\010\010\010\010\010\010\000\000\000\000\011\000\
\\000\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\000\000\000\010\
\\000\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\000\000\000\000\
\\000"
),
 (11, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\012\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (12, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\013\013\013\013\013\013\013\013\013\013\000\000\000\000\000\000\
\\000\013\013\013\013\013\013\013\013\013\013\013\013\013\013\013\
\\013\013\013\013\013\013\013\013\013\013\013\000\000\000\000\013\
\\000\013\013\013\013\013\013\013\013\013\013\013\013\013\013\013\
\\013\013\013\013\013\013\013\013\013\013\013\000\000\000\000\000\
\\000"
),
 (14, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\015\015\015\015\015\015\015\015\015\015\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (16, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\017\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (17, 
"\017\017\017\017\017\017\017\017\017\017\000\017\017\017\017\017\
\\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\
\\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\
\\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\
\\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\
\\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\
\\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\
\\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\
\\017"
),
 (18, 
"\000\000\000\000\000\000\000\000\000\019\019\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\019\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
(0, "")]
fun f x = x 
val s = map f (rev (tl (rev s))) 
exception LexHackingError 
fun look ((j,x)::r, i: int) = if i = j then x else look(r, i) 
  | look ([], i) = raise LexHackingError
fun g {fin=x, trans=i} = {fin=x, trans=look(s,i)} 
in Vector.fromList(map g 
[{fin = [], trans = 0},
{fin = [], trans = 1},
{fin = [], trans = 1},
{fin = [(N 26)], trans = 0},
{fin = [(N 12),(N 26)], trans = 4},
{fin = [(N 12)], trans = 4},
{fin = [(N 26)], trans = 6},
{fin = [], trans = 7},
{fin = [(N 24)], trans = 0},
{fin = [(N 26)], trans = 9},
{fin = [], trans = 10},
{fin = [], trans = 11},
{fin = [], trans = 12},
{fin = [(N 20)], trans = 12},
{fin = [(N 9),(N 26)], trans = 14},
{fin = [(N 9)], trans = 14},
{fin = [(N 26)], trans = 16},
{fin = [(N 6)], trans = 17},
{fin = [(N 2),(N 26)], trans = 18},
{fin = [(N 2)], trans = 18}])
end
structure StartStates =
	struct
	datatype yystartstate = STARTSTATE of int

(* start state definitions *)

val INITIAL = STARTSTATE 1;

end
type result = UserDeclarations.lexresult
	exception LexerError (* raised if illegal leaf action tried *)
end

structure YYPosInt : INTEGER = Int
fun makeLexer yyinput =
let	val yygone0= YYPosInt.fromInt ~1
	val yyb = ref "\n" 		(* buffer *)
	val yybl = ref 1		(*buffer length *)
	val yybufpos = ref 1		(* location of next character to use *)
	val yygone = ref yygone0	(* position in file of beginning of buffer *)
	val yydone = ref false		(* eof found yet? *)
	val yybegin = ref 1		(*Current 'start state' for lexer *)

	val YYBEGIN = fn (Internal.StartStates.STARTSTATE x) =>
		 yybegin := x

fun lex () : Internal.result =
let fun continue() = lex() in
  let fun scan (s,AcceptingLeaves : Internal.yyfinstate list list,l,i0) =
	let fun action (i,nil) = raise LexError
	| action (i,nil::l) = action (i-1,l)
	| action (i,(node::acts)::l) =
		case node of
		    Internal.N yyk => 
			(let fun yymktext() = substring(!yyb,i0,i-i0)
			     val yypos = YYPosInt.+(YYPosInt.fromInt i0, !yygone)
			open UserDeclarations Internal.StartStates
 in (yybufpos := i; case yyk of 

			(* Application actions *)

  12 => let val yytext=yymktext() in (*#line 52.35 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec"*) SHELL("id"        , yytext,     getNextTokenPos(yytext))    (*#line 258.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec.sml"*)
 end
| 2 => let val yytext=yymktext() in (*#line 48.18 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec"*) getNextTokenPos(yytext); lex()  (*#line 260.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec.sml"*)
 end
| 20 => let val yytext=yymktext() in (*#line 56.35 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec"*) SHELL(generateSchemaTokenName(yytext), yytext, getNextTokenPos(yytext))    (*#line 262.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec.sml"*)
 end
| 24 => let val yytext=yymktext() in (*#line 57.35 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec"*) SHELL("" , yytext, getNextTokenPos(yytext))    (*#line 264.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec.sml"*)
 end
| 26 => let val yytext=yymktext() in (*#line 59.35 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec"*) error("ignored an unprintable character: " ^ yytext); getNextTokenPos(yytext); lex()  (*#line 266.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec.sml"*)
 end
| 6 => let val yytext=yymktext() in (*#line 49.18 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec"*) getNextTokenPos(yytext); lex()  (*#line 268.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec.sml"*)
 end
| 9 => let val yytext=yymktext() in (*#line 51.35 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec"*) SHELL("integer"   , yytext,     getNextTokenPos(yytext))    (*#line 270.1 "C:\Users\Joseph\Coding\CSCI4220\Group_Project\Milestone_03\M3_Package\Domain-Template\Transformation\bin\target_tokens.spec.sml"*)
 end
| _ => raise Internal.LexerError

		) end )

	val {fin,trans} = Vector.sub(Internal.tab, s)
	val NewAcceptingLeaves = fin::AcceptingLeaves
	in if l = !yybl then
	     if trans = #trans(Vector.sub(Internal.tab,0))
	       then action(l,NewAcceptingLeaves
) else	    let val newchars= if !yydone then "" else yyinput 1024
	    in if (size newchars)=0
		  then (yydone := true;
		        if (l=i0) then UserDeclarations.eof ()
		                  else action(l,NewAcceptingLeaves))
		  else (if i0=l then yyb := newchars
		     else yyb := substring(!yyb,i0,l-i0)^newchars;
		     yygone := YYPosInt.+(!yygone, YYPosInt.fromInt i0);
		     yybl := size (!yyb);
		     scan (s,AcceptingLeaves,l-i0,0))
	    end
	  else let val NewChar = Char.ord(CharVector.sub(!yyb,l))
		val NewChar = if NewChar<128 then NewChar else 128
		val NewState = Char.ord(CharVector.sub(trans,NewChar))
		in if NewState=0 then action(l,NewAcceptingLeaves)
		else scan(NewState,NewAcceptingLeaves,l+1,i0)
	end
	end
(*
	val start= if substring(!yyb,!yybufpos-1,1)="\n"
then !yybegin+1 else !yybegin
*)
	in scan(!yybegin (* start *),nil,!yybufpos,!yybufpos)
    end
end
  in lex
  end
end
