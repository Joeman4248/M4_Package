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

(* ---------- Expressions ---------- *)

(* <expression> ::= <disjunction> *)
fun E( itree(inode("expression",_), [ disjunction ]), m ) = E(disjunction, m)

(* <disjunction> ::= <disjunction> "||" <conjunction>
                   | <conjunction> *)
  | E( itree(inode("disjunction",_),
            [
                disjunction,
                itree(inode("||",_), [] ),
                conjunction
            ]
        ), m
    ) = let
            val (v1, m1) = E(disjunction, m)
            val term1 = dvToBool(v1)
        in
            if term1 then
                (v1, m1)
            else
                E(conjunction, m1)
        end

  | E( itree(inode("disjunction",_), [ conjunction ]), m ) = E(conjunction, m)

(* <conjunction> ::= <conjunction> "&&" <equality>
                   | <equality> *)
  | E( itree(inode("conjunction",_),
            [
                conjunction,
                itree(inode("&&",_), [] ),
                equality
            ]
        ), m
    ) = let
            val (v1, m1) = E(conjunction, m)
            val term1 = dvToBool(v1)
        in
            if not term1 then
                (v1, m1)
            else
                E(equality, m1)
        end

  | E( itree(inode("conjunction",_), [ equality ]), m ) = E(equality, m)

(* <equality> ::= <equality> "==" <relational>
                | <equality> "!=" <relational>
                | <relational> *)
  | E( itree(inode("equality",_),
            [
                equality,
                itree(inode("==",_), []),
                relational
            ]
        ), m
    ) = let
            val (term1, m1) = E(equality, m)
            val (term2, m2) = E(relational, m1)
        in
            (Boolean (term1 = term2), m2)
        end

  | E( itree(inode("equality",_),
            [
                equality,
                itree(inode("!=",_), []),
                relational
            ]
        ), m
    ) = let
            val (term1, m1) = E(equality, m)
            val (term2, m2) = E(relational, m1)
        in
            (Boolean (term1 <> term2), m2)
        end

  | E( itree(inode("equality",_), [ relational ]), m ) = E(relational, m)

(* <relational> ::= <relational> "<" <additive>
                  | <relational> ">" <additive>
                  | <relational> "<=" <additive>
                  | <relational> ">=" <additive>
                  | <additive> *)
  | E( itree(inode("relational",_),
            [
                relational,
                itree(inode("<",_), []),
                additive
            ]
        ), m
    ) = let
            val (v1, m1) = E(relational, m)
            val (v2, m2) = E(additive, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Boolean (term1 < term2), m2)
        end

  | E( itree(inode("relational",_),
            [
                relational,
                itree(inode(">",_), []),
                additive
            ]
        ), m
    ) = let
            val (v1, m1) = E(relational, m)
            val (v2, m2) = E(additive, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Boolean (term1 > term2), m2)
        end

  | E( itree(inode("relational",_),
            [
                relational,
                itree(inode("<=",_), []),
                additive
            ]
        ), m
    ) = let
            val (v1, m1) = E(relational, m)
            val (v2, m2) = E(additive, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Boolean (term1 <= term2), m2)
        end

  | E( itree(inode("relational",_),
            [
                relational,
                itree(inode(">=",_), []),
                additive
            ]
        ), m
    ) = let
            val (v1, m1) = E(relational, m)
            val (v2, m2) = E(additive, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Boolean (term1 >= term2), m2)
        end

  | E( itree(inode("relational",_), [ additive ]), m ) = E(additive, m)

(* <additive> ::= <additive> "+" <multiplicative>
                | <additive> "-" <multiplicative>
                | <multiplicative> *)
  | E( itree(inode("additive",_),
            [
                additive,
                itree(inode("+",_), []),
                multiplicative
            ]
        ), m
    ) = let
            val (v1, m1) = E(additive, m)
            val (v2, m2) = E(multiplicative, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Integer (term1 + term2), m2)
        end

  | E( itree(inode("additive",_),
            [
                additive,
                itree(inode("-",_), []),
                multiplicative
            ]
        ), m
    ) = let
            val (v1, m1) = E(additive, m)
            val (v2, m2) = E(multiplicative, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Integer (term1 - term2), m2)
        end

  | E( itree(inode("additive",_), [ multiplicative ]), m ) = E(multiplicative, m)

(* <multiplicative> ::= <multiplicative> "*" <negation>
                      | <multiplicative> "/" <negation>
                      | <multiplicative> "%" <negation>
                      | <negation> *)
  | E( itree(inode("multiplicative",_),
            [
                multiplicative,
                itree(inode("*",_), []),
                negation
            ]
        ), m
    ) = let
            val (v1, m1) = E(multiplicative, m)
            val (v2, m2) = E(negation, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Integer (term1 * term2), m2)
        end

  | E( itree(inode("multiplicative",_),
            [
                multiplicative,
                itree(inode("/",_), []),
                negation
            ]
        ), m
    ) = let
            val (v1, m1) = E(multiplicative, m)
            val (v2, m2) = E(negation, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Integer (term1 div term2), m2)
        end

  | E( itree(inode("multiplicative",_),
            [
                multiplicative,
                itree(inode("%",_), []),
                negation
            ]
        ), m
    ) = let
            val (v1, m1) = E(multiplicative, m)
            val (v2, m2) = E(negation, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Integer (term1 mod term2), m2)
        end

  | E( itree(inode("multiplicative",_), [ negation ]), m ) = E(negation, m)

(* <negation> ::= "!" <negation>
                | "~" <negation>
                | <exponent> *)
  | E( itree(inode("negation",_),
            [
                itree(inode("!",_), []),
                negation
            ]
        ), m
    ) = let
            val (v1, m1) = E(negation, m)
            val term1 = dvToBool(v1)
        in
            (Boolean (not term1), m1)
        end

  | E( itree(inode("negation",_),
            [
                itree(inode("~",_), []),
                negation
            ]
        ), m
    ) = let
            val (v1, m1) = E(negation, m)
            val term1 = dvToInt(v1)
        in
            (Integer (~term1), m1)
        end

  | E( itree(inode("negation",_), [ exponent ]), m ) = E(exponent, m)

(* <exponent> ::= <absolute> "^" <exponent>
                | <absolute> *)
  | E( itree(inode("exponent",_),
            [
                absolute,
                itree(inode("^",_), []),
                exponent
            ]
        ), m
    ) = let
            fun exp(x, 0) = 1
              | exp(x, y) = x * exp(x, y - 1)

            val (v1, m1) = E(absolute, m)
            val (v2, m2) = E(exponent, m1)
            val term1 = dvToInt(v1)
            val term2 = dvToInt(v2)
        in
            (Integer (exp(term1, term2)), m2)
        end

  | E( itree(inode("exponent",_), [ absolute ]), m ) = E(absolute, m)

(* <absolute> ::= "abs" "(" <expression> ")"
                | <base> *)
  | E( itree(inode("absolute",_),
            [
                itree(inode("abs",_), []),
                itree(inode("(",_), []),
                expression,
                itree(inode(")",_), [])
            ]
        ), m
    ) = let
            val (v1, m1) = E(expression, m)
            val term1 = dvToInt(v1)
        in
            if term1 < 0 then
                (Integer (~term1), m1)
            else
                (Integer term1, m1)
        end

  | E( itree(inode("absolute",_), [ base ]), m ) = E(base, m)

(* <base> ::= "(" <expression> ")" | <increment>
            | id  | integer | "true" | "false" *)
  | E( itree(inode("base",_), [ itree(inode("true",_), [])  ]), m) = (Boolean true,  m)

  | E( itree(inode("base",_), [ itree(inode("false",_), []) ]), m) = (Boolean false, m)

  | E( itree(inode("base",_),
            [
                itree(inode("(",_), []),
                expression,
                itree(inode(")",_), [])
            ]
        ), m
    ) = E(expression, m)

  | E( itree(inode("base",_), [ child ]), m) = E(child, m)


  | E( itree(inode("integer",_), [ integer ]), m) =
        let
            val value = valOf(Int.fromString(getLeaf(integer)))
        in
            (Integer value, m)
        end

  | E( itree(inode("id",_), [ id ]), m ) =
        let
            val value = accessStore(getLoc(accessEnv(getLeaf(id), m)), m)
        in
            (value, m)
        end

(* <increment> ::= id "++"
                 | id "--"
                 | "++" id
                 | "--" id *)
  | E( itree(inode("increment",_), [ id, itree(inode("++",_), []) ]), m) =
        let
            val loc = getLoc(accessEnv(getLeaf(id), m))
            val v1 = accessStore(loc, m)
            val v2 = Integer (dvToInt(v1) + 1)
        in
            (v1, updateStore(loc, v2, m))
        end

  | E( itree(inode("increment",_), [ id, itree(inode("--",_), []) ]), m) =
        let
            val loc = getLoc(accessEnv(getLeaf(id), m))
            val v1 = accessStore(loc, m)
            val v2 = Integer (dvToInt(v1) - 1)

        in
            (v1, updateStore(loc, v2, m))
        end

  | E( itree(inode("increment",_), [ itree(inode("++",_), []), id ]), m) =
        let
            val loc = getLoc(accessEnv(getLeaf(id), m))
            val v1 = accessStore(loc, m)
            val v2 = Integer (dvToInt(v1) + 1)
        in
            (v2, updateStore(loc, v2, m))
        end

  | E( itree(inode("increment",_), [ itree(inode("--",_), []), id ]), m) =
        let
            val loc = getLoc(accessEnv(getLeaf(id), m))
            val v1 = accessStore(loc, m)
            val v2 = Integer (dvToInt(v1) - 1)
        in
            (v2, updateStore(loc, v2, m))
        end

  | E( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")

  | E _ = raise Fail("error in Semantics.M - this should never occur")

(* ---------- Statements ---------- *)

(* <prog> ::= <stmtList> . *)
fun M( itree( inode("prog",_), [ stmt_list ] ), m ) = M( stmt_list, m )

(* <stmtList> ::= <stmt> <stmtList> | . *)
  | M( itree( inode("stmtList",_), [ itree(inode("",_), []) ] ), m ) = m
  | M( itree( inode("stmtList",_),
            [
                stmt,
                stmtList
            ]
        ), m
    ) = M( stmtList, M(stmt, m) )

(* <stmt> ::= <declare> ";"
            | <assign> ";"
            | <initialize> ";"
            | <output> ";"
            | <block>
            | <conditional>
            | <iteration> *)
  | M( itree( inode("stmt",_), [ child,
                                 itree(inode(";",_), []) ] ), m) = M(child, m)

  | M( itree( inode("stmt",_), [ child ] ), m) = M(child, m)

(* <declare> ::= "int"  id
               | "bool" id *)
  | M( itree(inode("declare",_), [ itree(inode("int",_), [] ),  id ]), m) = updateEnv(getLeaf(id), INT, m)

  | M( itree(inode("declare",_), [ itree(inode("bool",_), [] ), id ]), m) = updateEnv(getLeaf(id), BOOL, m)

(* <assign> ::= id "=" <expression> | <increment> *)
  | M( itree(inode("assign",_),
            [
                id,
                itree(inode("=",_), [] ),
                expression
            ]
        ), m
    ) = let
            val (v1, m1) = E(expression, m)
        in
            (* updateStore( location, value, model ) *)
            updateStore(getLoc(accessEnv(getLeaf(id), m1)), v1, m1)
        end

  | M( itree(inode("assign",_), [ increment ]), m) =
        let
            val (v1, m1) = E(increment, m)
        in
            m1
        end

(* <output> ::= "print" "(" <expression> ")" *)
  | M( itree(inode("output",_),
            [
                itree(inode("print",_), [] ),
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] )
            ]
        ), m
    ) = let
            val (v1, m1) = E(expression, m)
        in
            print(dvToString(v1) ^ "\n");
            m1
        end

(* <block> ::= "{" <stmtList> "}" *)
  | M( itree(inode("block",_),
            [
                itree(inode("{",_), [] ),
                stmtList,
                itree(inode("}",_), [] )
            ]
        ), m
    ) = let
            val (env0, loc0, s0) = m
            val (env1, loc1, s1) = M(stmtList, m)
        in
            (env0, loc0, s1)
        end

(* <conditional> ::= "if" "(" <expression> ")" <block>
                   | "if" "(" <expression> ")" <block> "else" <block> *)
  | M( itree(inode("conditional",_),
            [
                itree(inode("if",_), [] ),
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] ),
                block
            ]
        ), m
    ) = let
            val (v1, m1) = E(expression, m)
            val cond = dvToBool(v1)
        in
            if cond then
                M(block, m1)
            else
                m1
        end

  | M( itree(inode("conditional",_),
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
            val (v1, m1) = E(expression, m)
            val cond = dvToBool(v1)
        in
            if cond then
                M(block1, m1)
            else
                M(block2, m1)
        end

(* <iteration> ::= "while" "(" <expression> ")" <block>
                 | "for" "(" <assign> ";" <expression> ";" <loopIncrement> ")" <block> *)
  | M( itree(inode("iteration",_),
            [
                itree(inode("while",_), [] ),
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] ),
                block
            ]
        ), m
    ) = let
            fun whileLoopHelper(expression, block, m) =
                let
                    val (v1, m1) = E(expression, m)
                    val cond = dvToBool(v1)
                in
                    if cond then
                        whileLoopHelper(expression, block, M(block, m1))
                    else
                        m1
                end
        in
            whileLoopHelper(expression, block, m)
        end

  | M( itree(inode("iteration",_),
            [
                itree(inode("for",_), [] ),
                itree(inode("(",_), [] ), assign1,
                itree(inode(";",_), [] ), expression,
                itree(inode(";",_), [] ), assign2,
                itree(inode(")",_), [] ), block
            ]
        ), m
    ) = let
            val m1 = M(assign1, m)
            fun forLoopHelper(expression, block, assign2, m) =
                let
                    val (v1, m1) = E(expression, m)
                    val cond = dvToBool(v1)
                in
                    if cond then
                        let
                            val m2 = M(block, m1)
                            val m3 = M(assign2, m2)
                        in
                            forLoopHelper(expression, block, assign2, m3)
                        end
                    else
                        m1
                end
        in
            forLoopHelper(expression, block, assign2, m1)
        end

  | M( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")

  | M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)
