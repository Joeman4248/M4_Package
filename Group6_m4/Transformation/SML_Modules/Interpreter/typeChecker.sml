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
fun typeOf( itree(inode("expression",_), [ disjunction ]), m ) = typeOf(disjunction, m)

(* <disjunction> ::= <disjunction> "||" <conjunction>
                   | <conjunction> *)
  | typeOf( itree(inode("disjunction",_),
            [
                disjunction,
                itree(inode("||",_), [] ),
                conjunction
            ]
        ), m
    ) = let
            val t1 = typeOf(disjunction, m)
            val t2 = typeOf(conjunction, m)
        in
            if t1 = BOOL andalso t2 = BOOL then
                BOOL
            else
                ERROR
        end

  | typeOf( itree(inode("disjunction",_), [ conjunction ]), m ) = typeOf(conjunction, m)

(* <conjunction> ::= <conjunction> "&&" <equality>
                   | <equality> *)
  | typeOf( itree(inode("conjunction",_),
            [
                conjunction,
                itree(inode("&&",_), [] ),
                equality
            ]
        ), m
    ) = let
            val t1 = typeOf(conjunction, m)
            val t2 = typeOf(equality, m)
        in
            if t1 = BOOL andalso t2 = BOOL then
                BOOL
            else
                ERROR
        end

  | typeOf( itree(inode("conjunction",_), [ equality ]), m ) = typeOf(equality, m)

(* <equality> ::= <equality> "==" <relational>
                | <equality> "!=" <relational>
                | <relational> *)
  | typeOf( itree(inode("equality",_),
            [
                equality,
                itree(inode("==",_), [] ),
                relational
            ]
        ), m
    ) = let
            val t1 = typeOf(equality, m)
            val t2 = typeOf(relational, m)
        in
            if t1 <> ERROR andalso t1 = t2 then
                BOOL
            else
                ERROR
        end

  | typeOf( itree(inode("equality",_),
            [
                equality,
                itree(inode("!=",_), [] ),
                relational
            ]
        ), m
    ) = let
            val t1 = typeOf(equality, m)
            val t2 = typeOf(relational, m)
        in
            if t1 <> ERROR andalso t1 = t2 then
                BOOL
            else
                ERROR
        end

  | typeOf( itree(inode("equality",_), [ relational ]), m ) = typeOf(relational, m)

(* <relational> ::= <relational> "<" <additive>
                  | <relational> ">" <additive>
                  | <relational> "<=" <additive>
                  | <relational> ">=" <additive>
                  | <additive> *)
  | typeOf( itree(inode("relational",_),
            [
                relational,
                itree(inode("<",_), [] ),
                additive
            ]
        ), m
    ) = let
            val t1 = typeOf(relational, m)
            val t2 = typeOf(additive, m)
        in
            if t1 = INT andalso t2 = INT then
                BOOL
            else
                ERROR
        end

  | typeOf( itree(inode("relational",_),
            [
                relational,
                itree(inode(">",_), [] ),
                additive
            ]
        ), m
    ) = let
            val t1 = typeOf(relational, m)
            val t2 = typeOf(additive, m)
        in
            if t1 = INT andalso t2 = INT then
                BOOL
            else
                ERROR
        end

  | typeOf( itree(inode("relational",_),
            [
                relational,
                itree(inode("<=",_), [] ),
                additive
            ]
        ), m
    ) = let
            val t1 = typeOf(relational, m)
            val t2 = typeOf(additive, m)
        in
            if t1 = INT andalso t2 = INT then
                BOOL
            else
                ERROR
        end

  | typeOf( itree(inode("relational",_),
            [
                relational,
                itree(inode(">=",_), [] ),
                additive
            ]
        ), m
    ) = let
            val t1 = typeOf(relational, m)
            val t2 = typeOf(additive, m)
        in
            if t1 = INT andalso t2 = INT then
                BOOL
            else
                ERROR
        end

  | typeOf( itree(inode("relational",_), [ additive ]), m ) = typeOf(additive, m)

(* <additive> ::= <additive> "+" <multiplicative>
                | <additive> "-" <multiplicative>
                | <multiplicative> *)
  | typeOf( itree(inode("additive",_),
            [
                additive,
                itree(inode("+",_), [] ),
                multiplicative
            ]
        ), m
    ) = let
            val t1 = typeOf(additive, m)
            val t2 = typeOf(multiplicative, m)
        in
            if t1 = INT andalso t2 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("additive",_),
            [
                additive,
                itree(inode("-",_), [] ),
                multiplicative
            ]
        ), m
    ) = let
            val t1 = typeOf(additive, m)
            val t2 = typeOf(multiplicative, m)
        in
            if t1 = INT andalso t2 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("additive",_), [ multiplicative ]), m ) = typeOf(multiplicative, m)

(* <multiplicative> ::= <multiplicative> "*" <negation>
                      | <multiplicative> "/" <negation>
                      | <multiplicative> "%" <negation>
                      | <negation> *)
  | typeOf( itree(inode("multiplicative",_),
            [
                multiplicative,
                itree(inode("*",_), [] ),
                negation
            ]
        ), m
    ) = let
            val t1 = typeOf(multiplicative, m)
            val t2 = typeOf(negation, m)
        in
            if t1 = INT andalso t2 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("multiplicative",_),
            [
                multiplicative,
                itree(inode("/",_), [] ),
                negation
            ]
        ), m
    ) = let
            val t1 = typeOf(multiplicative, m)
            val t2 = typeOf(negation, m)
        in
            if t1 = INT andalso t2 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("multiplicative",_),
            [
                multiplicative,
                itree(inode("%",_), [] ),
                negation
            ]
        ), m
    ) = let
            val t1 = typeOf(multiplicative, m)
            val t2 = typeOf(negation, m)
        in
            if t1 = INT andalso t2 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("multiplicative",_), [ negation ]), m ) = typeOf(negation, m)

(* <negation> ::= "!" <negation>
                | "~" <negation>
                | <exponent> *)
  | typeOf( itree(inode("negation",_),
            [
                itree(inode("!",_), [] ),
                negation
            ]
        ), m
    ) = let
            val t1 = typeOf(negation, m)
        in
            if t1 = BOOL then
                BOOL
            else
                ERROR
        end

  | typeOf( itree(inode("negation",_),
            [
                itree(inode("~",_), [] ),
                negation
            ]
        ), m
    ) = let
            val t1 = typeOf(negation, m)
        in
            if t1 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("negation",_), [ exponent ]), m ) = typeOf(exponent, m)

(* <exponent> ::= <absolute> "^" <exponent>
                | <absolute> *)
  | typeOf( itree(inode("exponent",_),
            [
                absolute,
                itree(inode("^",_), [] ),
                exponent
            ]
        ), m
    ) = let
            val t1 = typeOf(absolute, m)
            val t2 = typeOf(exponent, m)
        in
            if t1 = INT andalso t1 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("exponent",_), [ absolute ]), m ) = typeOf(absolute, m)

(* <absolute> ::= "abs" "(" <expression> ")"
                | <base> *)
  | typeOf( itree(inode("absolute",_),
            [
                itree(inode("abs",_), [] ),
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] )
            ]
        ), m
    ) = let
            val t1 = typeOf(expression, m)
        in
            if t1 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("absolute",_), [ base ]), m ) = typeOf(base, m)

(* <base> ::= id | boolean | integer
            | "(" <expression> ")" | <increment> *)
  | typeOf( itree(inode("base",_), [ child ]), m ) = typeOf(child, m)

  | typeOf( itree(inode("base",_),
            [
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] )
            ]
        ), m
    ) = typeOf(expression, m)

(* <increment> ::= id "++"
                 | id "--"
                 | "++" id
                 | "--" id *)
  | typeOf( itree(inode("increment",_),
            [
                id,
                itree(inode("++",_), [] )
            ]
        ), m
    ) = let
            val t1 = typeOf(id, m)
        in
            if t1 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("increment",_),
            [
                id,
                itree(inode("--",_), [] )
            ]
        ), m
    ) = let
            val t1 = typeOf(id, m)
        in
            if t1 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("increment",_),
            [
                itree(inode("++",_), [] ),
                id
            ]
        ), m
    ) = let
            val t1 = typeOf(id, m)
        in
            if t1 = INT then
                INT
            else
                ERROR
        end

  | typeOf( itree(inode("increment",_),
            [
                itree(inode("--",_), [] ),
                id
            ]
        ), m
    ) = let
            val t1 = typeOf(id, m)
        in
            if t1 = INT then
                INT
            else
                ERROR
        end

(* id | boolean | integer *)
  | typeOf( id as itree(inode("id",_), [ _ ]), m ) = getType(accessEnv(getLeaf(id), m))

  | typeOf( itree(inode("boolean",_), [ _ ]), m) = BOOL

  | typeOf( itree(inode("integer",_), [ _ ]), m) = INT

  | typeOf( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")
  | typeOf _ = raise Fail("Error in Model.typeCheck - this should never occur")

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
  | typeCheck( itree( inode("declare",_),
        [ itree(inode("int",_), []),  id ] ), m ) = updateEnv(getLeaf(id), INT,  m)

  | typeCheck( itree( inode("declare",_),
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
            val t2 = getType(accessEnv(getLeaf(id), m))
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
                raise Fail("ERROR: expected " ^ typeToString(BOOL) ^ ", but got " ^ typeToString(t1))
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
                raise Fail("ERROR: expected " ^ typeToString(BOOL) ^ ", but got " ^ typeToString(t1))
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
                raise Fail("ERROR: expected " ^ typeToString(BOOL) ^ ", but got " ^ typeToString(t1))
        end

  | typeCheck( itree(inode("iteration",_),
            [
                itree(inode("for",_), [] ),
                itree(inode("(",_), [] ), assign,
                itree(inode(";",_), [] ), expression,
                itree(inode(";",_), [] ), loopIncrement,
                itree(inode(")",_), [] ), block
            ]
        ), m
    ) = let
            val m1 = typeCheck(assign, m)
            val t1 = typeOf(expression, m1)
            val m2 = typeCheck(block, m1)
            val m3 = typeCheck(loopIncrement, m2)
        in
            if t1 = BOOL then
                m
            else
                raise Fail("ERROR: expected " ^ typeToString(BOOL) ^ ", but got " ^ typeToString(t1))
        end

(* <loopIncrement> ::= <assign> | <increment> *)
  | typeCheck( itree( inode("loopIncrement",_),
            [
                itree( inode("assign",_), [ assign ] )
            ]
        ), m
    ) = typeCheck(assign, m)

  | typeCheck( itree( inode("loopIncrement",_),
            [
                itree( inode("increment",_), [ increment ] )
            ]
        ), m
    ) = let
            val t1 = typeOf(increment, m)
        in
            if t1 = INT then
                m
            else
                raise Fail("ERROR: expected " ^ typeToString(INT) ^ ", but got " ^ typeToString(t1))
        end

  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)
