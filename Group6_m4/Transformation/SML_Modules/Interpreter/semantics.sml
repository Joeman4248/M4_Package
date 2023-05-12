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

(* <assign> ::= id "=" <expression> *)

(* <output> ::= "print" "(" <expression> ")" *)

(* <conditional> ::= "if" "(" <expression> ")" <block>  *)
(* <conditional> ::= "if" "(" <expression> ")" <block> "else" <block> *)

(* <iteration> ::= "while" "(" <expression> ")" <block>  *)
(* <iteration> ::= "for" "(" <assign> ";" <expression> ";" <loopIncrement> ")" <block> *)

(* <loopIncrement> ::= <assign> | <increment> *)

(* ---------- Boolean Expressions ---------- *)

(* <expression> ::= <disjunction> *)
fun E( itree(inode("expression",_), [ disjunction ]), m ) = E(disjunction, m)

(* <disjunction> ::= <disjunction> "||" <conjunction> 
                   | <conjunction> *)
fun E( itree(inode("disjunction",_),
        [
            disjunction,
            itree(inode("||",_), [] ),
            conjunction
        ]
    ), m) = let
                val (term1, m1) = E(disjunction, m)
            in
                if term1 then
                    (term1, m1)
                else
                    E(conjunction, m1)
            end
            
  | E( itree(inode("disjunction",_), [ conjunction ]), m ) = E(conjunction, m)

(* <conjunction> ::= <conjunction> "&&" <equality> 
                   | <equality> *)
fun E( itree(inode("conjunction",_),
        [
            conjunction,
            itree(inode("&&",_), [] ),
            equality
        ]
    ), m) = let
                val (term1, m1) = E(conjunction, m)
            in
                if not term1 then
                    (term1, m1)
                else
                    E(equality, m1)
            end
            
  | E( itree(inode("conjunction",_), [ equality ]), m ) = E(equality, m)

(* <equality> ::= <equality> "==" <relational> 
                | <equality> "!=" <relational> 
                | <relational> *)
fun E( itree(inode("equality"_),
        [
            equality,
            itree(inode("==",_), []),
            relational
        ]
    ), m) = let
                val (term1, m1) = E(equality, m)
                val (term2, m2) = E(relational, m1)
            in
                (term1 <> term2, m2)
            end

  | E( itree(inode("equality"_), 
        [
            equality,
            itree(inode("!=",_), []),
            relational
        ]
    ), m) = let
                val (term1, m1) = E(equality, m)
                val (term2, m2) = E(relational, m1)
            in
                (term1 <> term2, m2)
            end

(* <relational> ::= <relational> "<" <additive> 
                  | <relational> ">" <additive> 
                  | <relational> "<=" <additive> 
                  | <relational> ">=" <additive> 
                  | <additive> *)

fun E( itree(inode("relational"_), 
        [
            relational,
            itree(inode("<"_), []),
            additive
        ]
    ), m) = let
                val (term1, m1) = E(relational, m)
                val (term2, m2) = E(additive, m1)
            in
                (term1 < term2, m2)
            end

  | E( itree(inode("relational"_), 
        [
            relational,
            itree(inode(">"_), []),
            additive
        ]
    ), m) = let
                val (term1, m1) = E(relational, m)
                val (term2, m2) = E(additive, m1)
            in
                (term1 > term2, m2)
            end
            
  | E( itree(inode("relational"_), 
        [
            relational,
            itree(inode("<="_), []),
            additive
        ]
    ), m) = let
                val (term1, m1) = E(relational, m)
                val (term2, m2) = E(additive, m1)
            in
                (term1 <= term2, m2)
            end

  | E( itree(inode("relational"_), 
        [
            relational,
            itree(inode(">="_), []),
            additive
        ]
    ), m) = let
                val (term1, m1) = E(relational, m)
                val (term2, m2) = E(additive, m1)
            in
                (term1 >= term2, m2)
            end
            
  | E( itree(inode("relational",_), [ equality ]), m ) = E(additive, m)

(* ---------- Integer Expressions ----- *)

(* <additive> ::= <additive> "+" <multiplicative> 
                | <additive> "-" <multiplicative> 
                | <multiplicative> *)
fun E( itree(inode("additive"_), 
        [
            additive,
            itree(inode("+"_), []),
            multiplicative
        ]
    ), m) = let
                val (term1, m1) = E(additive, m)
                val (term2, m2) = E(multiplicative, m1)
            in
                (term1 + term2, m2)
            end
            
  | E( itree(inode("additive"_), 
        [
            additive,
            itree(inode("-"_), []),
            multiplicative
        ]
    ), m) = let
                val (term1, m1) = E(additive, m)
                val (term2, m2) = E(multiplicative, m1)
            in
                (term1 - term2, m2)
            end

  | E( itree(inode("additive",_), [ multiplicative ]), m ) = E(multiplicative, m)

(* <multiplicative> ::= <multiplicative> "*" <negation> 
                      | <multiplicative> "/" <negation> 
                      | <multiplicative> "%" <negation> 
                      | <negation> *)

(* <negation> ::= "!" <negation> 
                | "~" <negation> 
                | <exponent> *)

(* <exponent> ::= <absolute> "^" <exponent> 
                | <absolute> *)

(* <absolute> ::= "abs" "(" <expression> ")" 
                | <base> *)

(* <base> ::= "(" <expression> ")" | <increment> 
            | id | boolean | integer *)

(* <increment> ::= id "++" 
                 | id "--" 
                 | "++" id 
                 | "--" id *)

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)
