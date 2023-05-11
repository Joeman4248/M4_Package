(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

(* ---------- Statements ---------- *)

(* <prog> ::= <stmtList> . *)
fun M( itree( inode("prog",_), [ stmt_list ] ), m ) = M( stmt_list, m )
        
  | M( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")

(* <stmtList> ::= <stmt> <stmtList> | . *)
fun M( itree( inode("stmtList",_), [ itree(inode("",_), []) ] ), m ) = m
  | M( itree( inode("stmtList",_), 
        [ 
            stmt, 
            stmtList 
        ]
    ), m ) = M( stmtList, M(stmt, m) )

(* <stmt> ::= <block>  *)
(* <stmt> ::= <declare> ";"  *)
(* <stmt> ::= <assign> ";"  *)
(* <stmt> ::= <initialize> ";" *)
(* <stmt> ::= <output> ";"  *)
(* <stmt> ::= <conditional>  *)
(* <stmt> ::= <iteration>  *)

(* <declare> ::= "int"  id *)
(* <declare> ::= "bool" id *)

(* <block> ::= "{" <stmtList> "}" *)

(* <assign> ::= id "=" <expression> *)

(* <output> ::= "print" "(" <expression> ")" *)

(* <conditional> ::= "if" "(" <expression> ")" <block>  *)
(* <conditional> ::= "if" "(" <expression> ")" <block> "else" <block> *)

(* <iteration> ::= "while" "(" <expression> ")" <block>  *)
(* <iteration> ::= "for" "(" <assign> ";" <expression> ";" <loopIncrement> ")" <block> *)

(* <loopIncrement> ::= <assign> | <increment> *)

(* ---------- Boolean Expressions ---------- *)

(* <expression> ::= <disjunction> *)

(* <disjunction> ::= <disjunction> "||" <conjunction>  *)
(* <disjunction> ::= <conjunction> *)

(* <conjunction> ::= <conjunction> "&&" <equality>  *)
(* <conjunction> ::= <equality> *)

(* <equality> ::= <equality> "==" <relational>  *)
(* <equality> ::= <equality> "!=" <relational>  *)
(* <equality> ::= <relational> *)

(* <relational> ::= <relational> "<" <additive>  *)
(* <relational> ::= <relational> ">" <additive>  *)
(* <relational> ::= <relational> "<=" <additive>  *)
(* <relational> ::= <relational> ">=" <additive>  *)
(* <relational> ::= <additive> *)

(* ---------- Integer Expressions ---------- *)

(* <additive> ::= <additive> "+" <multiplicative>  *)
(* <additive> ::= <additive> "-" <multiplicative>  *)
(* <additive> ::= <multiplicative> *)

(* <multiplicative> ::= <multiplicative> "*" <negation>  *)
(* <multiplicative> ::= <multiplicative> "/" <negation>  *)
(* <multiplicative> ::= <multiplicative> "%" <negation>  *)
(* <multiplicative> ::= <negation> *)

(* <negation> ::= "!" <negation>  *)
(* <negation> ::= "~" <negation>  *)
(* <negation> ::=  <exponent> *)

(* <exponent> ::= <absolute> "^" <exponent>  *)
(* <exponent> ::= <absolute> *)

(* <absolute> ::= "abs" "(" <expression> ")"  *)
(* <absolute> ::= <base> *)

(* <base> ::= "(" <expression> ")" | <increment>  *)
(* <base> ::= id | boolean | integer *)

(* <increment> ::= id "++"  *)
(* <increment> ::= id "--"  *)
(* <increment> ::= "++" id  *)
(* <increment> ::= "--" id  *)

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)
