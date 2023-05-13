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
                                         itree(inode(";",_), []) ] ), m) = typeCheck(child, m)

  | typeCheck( itree( inode("stmt",_), [ child ] ), m) = typeCheck(child, m)

(* <declare> ::= "int"  id
               | "bool" id *)
  | typeCheck( itree( inode("declare"),
        [ itree(inode("int",_), []),  id ] ), m ) = updateEnv(getLeaf(id), INT,  m)

  | typeCheck( itree( inode("declare"),
        [ itree(inode("bool",_), []), id ] ), m ) = updateEnv(getLeaf(id), BOOL, m)

(* <assign> ::= id "=" <expression> *)
  | typeCheck( itree( inode("assign",_),
            [
                id,
                itree(inode("=",_), []),
                expression
            ]
        ), m
    ) = let
            val t1 = typeOf(expression, m)
            val t2 = getType(accessEnv(id, m), m)
        in
            if t1 = t2 then
                m
            else
                raise Fail("ERROR: cannot assign " ^ typeToString(t1) ^ " to variable of type: " ^ typeToString(t2))
        end

(* <output> ::= "print" "(" <expression> ")" *)
  | typeCheck( itree( inode("output",_),
            [
                itree(inode("print",_), [] ),
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] )
            ]
        ), m
    ) = let
            val t1 = typeOf(expression, m)
        in
            if t1 <> ERROR then
                m
            else
                raise Fail("ERROR: cannot print expression of type: " ^ typeToString(t1))
        end

(* <block> ::= "{" <stmtList> "}" *)
  | typeCheck( itree(inode("block",_),
            [
                itree(inode("{",_), [] ),
                stmtList,
                itree(inode("}",_), [] )
            ]
        ), m
    ) = let
            val m1 = typeCheck(stmtList, m)
        in
            m
        end

(* <conditional> ::= "if" "(" <expression> ")" <block>
                   | "if" "(" <expression> ")" <block> "else" <block> *)
  | typeCheck( itree(inode("conditional",_),
            [
                itree(inode("if",_), [] ),
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] ),
                block
            ]
        ), m
    ) = let
            val t1 = typeOf(expression, m)
            val m1 = typeCheck(block, m)
        in
            if t1 = BOOL then
                m
            else
                raise Fail("ERROR: expected " ^ typeToString(BOOL) ^ ", but received " ^ typeToString(t1))
        end

  | typeCheck( itree(inode("conditional",_),
            [
                itree(inode("if",_), [] ),
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] ),
                block1,
                itree(inode("else",_), [] ),
                block2
            ]
        ), m
    ) = let
            val t1 = typeOf(expression, m)
            val m1 = typeCheck(block1, m)
            val m2 = typeCheck(block2, m1)
        in
            if t1 = BOOL then
                m
            else
                raise Fail("ERROR: expected " ^ typeToString(BOOL) ^ ", but received " ^ typeToString(t1))
        end

(* <iteration> ::= "while" "(" <expression> ")" <block>
                 | "for" "(" <assign> ";" <expression> ";" <loopIncrement> ")" <block> *)
  | typeCheck( itree(inode("iteration",_),
            [
                itree(inode("while",_), [] ),
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] ),
                block
            ]
        ), m
    ) = let
            val t1 = typeOf(expression, m)
        in
            if t1 = BOOL then
                m
            else
                raise Fail("ERROR: expected " ^ typeToString(BOOL) ^ ", but received " ^ typeToString(t1))
        end

  | typeCheck( itree(inode("iteration",_),
            [
                itree(inode("for",_), [] ),
                itree(inode("(",_), [] ), assign,
                itree(inode(";",_), [] ), expression,
                itree(inode(";",_), [] ), loopIncrement,
                itree(inode(")",_), [] ),
                block
            ]
        ), m
    ) = let
            val m1 = typeCheck(assign, m)
            val t1 = typeOf(expression, m1)
            val m2 = typeCheck(block, m1)
            val m3 = typeCheck(loopIncrement, m3)
        in
            if t1 = BOOL then
                m
            else
                raise Fail("ERROR: expected " ^ typeToString(BOOL) ^ ", but received " ^ typeToString(t1))
        end

(* <loopIncrement> ::= <assign> | <increment> *)
  | typeCheck( itree( inode("loopIncrement",_),
            [
                assign as itree( inode("assign",_), [ _ ] )
            ]
        ), m
    ) = typeCheck(assign, m)

  | typeCheck( itree( inode("loopIncrement",_),
            [
                increment as itree( inode("increment",_), [ _ ] )
            ]
        ), m
    ) = let
            val t1 = typeOf(increment, m)
        in
            if t1 = INT then
                m
            else
                raise Fail("ERROR: expected " ^ typeToString(INT) ^ ", but received " ^ typeToString(t1))
        end

  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)
