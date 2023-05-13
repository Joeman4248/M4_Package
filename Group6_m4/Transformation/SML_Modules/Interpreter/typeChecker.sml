(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)

(* ---------- Expressions ---------- *)

(* <expression> ::= <disjunction> *)

(* <disjunction> ::= <disjunction> "||" <conjunction> 
                   | <conjunction> *)

(* <conjunction> ::= <conjunction> "&&" <equality> 
                | <equality> *)

(* <equality> ::= <equality> "==" <relational> 
                | <equality> "!=" <relational> 
                | <relational> *)

(* <relational> ::= <relational> "<" <additive> 
                  | <relational> ">" <additive> 
                  | <relational> "<=" <additive> 
                  | <relational> ">=" <additive> 
                  | <additive> *)

(* <additive> ::= <additive> "+" <multiplicative> 
                | <additive> "-" <multiplicative> 
                | <multiplicative> *)

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

(* <base> ::= id | boolean | integer
            | "(" <expression> ")" | <increment> *)

(* <increment> ::= id "++" 
                 | id "--" 
                 | "++" id 
                 | "--" id *)

(* ---------- Statements ---------- *)

(* <prog> ::= <stmtList> *)
fun typeCheck( itree(inode("prog",_), [ stmtList ] ), m ) = typeCheck(stmtList, m)

(* <stmtList> ::= <stmt> <stmtList> | *)
  | typeCheck( itree(inode("stmtList",_), 
            [
                stmt,
                stmtList
            ]
        ), m 
    ) = typeCheck(stmtList, typeCheck(stmt, m))

  | typeCheck( itree(inode("stmtList",_), [ itree(inode("",_), []) ] ), m ) = m

(* <stmt> ::= <block> 
            | <declare> ";" 
            | <assign> ";" 
            | <initialize> ";"
            | <output> ";" 
            | <conditional> 
            | <iteration> *)
  | typeCheck( itree( inode("stmt",_), [ child, 
                                         itree(inode(";",_), []) ] ), m) = M(child, m)

  | typeCheck( itree( inode("stmt",_), [ child ] ), m) = M(child, m)

(* <declare> ::= "int"  id
               | "bool" id *)
  | typeCheck( itree( inode("declare"), 
        [ itree(inode("int",_), []),  id ] ), m ) = updateEnv(getLeaf(id), INT,  m)

  | typeCheck( itree( inode("declare"), 
        [ itree(inode("bool",_), []), id ] ), m ) = updateEnv(getLeaf(id), BOOL, m)

(* <assign> ::= id "=" <expression> *)

(* <output> ::= "print" "(" <expression> ")" *)

(* <block> ::= "{" <stmtList> "}" *)

(* <conditional> ::= "if" "(" <expression> ")" <block> 
                   | "if" "(" <expression> ")" <block> "else" <block> *)

(* <iteration> ::= "while" "(" <expression> ")" <block> 
                 | "for" "(" <assign> ";" <expression> ";" <loopIncrement> ")" <block> *)

(* <loopIncrement> ::= <assign> | <increment> *)


  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)
