package sutd.compiler.simp.syntax

import sutd.compiler.simp.syntax.Lexer.*
import sutd.compiler.simp.syntax.SrcLoc.*
import sutd.compiler.simp.syntax.AST.*
import sutd.compiler.simp.syntax.Parsec.*
import org.scalactic.Bool

/* @jiande - 5th nov'25 Lab 1
    Task 1.1
    fix
        p_space
        p_spaecs
*/

object Parser {
    /**
     * S ::= X = E ; | return X ; | nop | if E { \overline{S} } else { \overline{S} } | while E { \overline{S} } 
     * E ::= E Op E | X | C | (E)
     * \overline{S} ::= S | S \overline{S}
     * Op ::= + | - | *  
     * C ::= 1 | 2 | ... | true | false 
     * X ::= a | b | c | d 
     * */


    import Stmt.*
    import Exp.*
    import Const.* 
    
    import LToken.*
    import Progress.*
    import Result.*

    case class PEnv(toks: List[LToken])

    /**
      * check whether the parsing is done based on the list of tokens left.
      *
      * @param env
      * @return boolean
      */
    def done(env:PEnv):Boolean = env match {
        case PEnv(Nil) => true
        case _ => false
    }

    /**
      * type class instance of ParserEnv[PEnv, LToken]
      */
    given penvParserEnv: ParserEnv[PEnv, LToken] = new ParserEnv[PEnv, LToken] {
        override def getTokens(env: PEnv): List[LToken] = env match {
            case PEnv(toks) => toks
        }
        override def getCol(env: PEnv): Int = env match {
            case PEnv(Nil) => -1
            case PEnv(tok :: toks) =>
                srcLoc(tok) match {
                    case SrcLoc(ln, col) => col
                }
        }
        override def getLine(env: PEnv): Int = env match {
            case PEnv(Nil) => -1
            case PEnv(tok :: toks) =>
                srcLoc(tok) match {
                    case SrcLoc(ln, col) => ln
                }
        }
        override def setTokens(ts: List[LToken])(env: PEnv): PEnv = env match {
            case PEnv(_) => PEnv(ts)
        }

    }
    /**
      * The top level parser
      */
    def parse:Parser[PEnv, List[Stmt]] = p_stmts

    /**
      * Parsing a sequence of statements, 
      * we skip the preceeding and the proceeding white spaces for each statement.
      * for individual statement parser, 
      * we only need to skip the whitespace in between.
      *
      * @return
      */
    def p_stmts:Parser[PEnv, List[Stmt]] = {
        def p_one:Parser[PEnv, Stmt] = for {
            _ <- p_spaces
            s <- p_stmt
            _ <- p_spaces
        } yield s
        many(p_one)
    } 

    /**
      * Parsing a statement
      *
      * @return
      */
    def p_stmt:Parser[PEnv, Stmt] = choice(p_assign)(choice(p_ret)(choice(p_nop)(choice(p_ifelse)(p_while))))

    /**
      * Parsing a Nop statement
      *
      * @return
      */
    def p_nop:Parser[PEnv, Stmt] = for {
        _ <- sat((tok:LToken) => tok match {
            case NopKW(src) => true 
            case _ => false 
        })
        _ <- p_spaces
        _ <- p_semicolon
    } yield Nop

    /**
      * Parsing an assignment statement
      *
      * @return
      */
    def p_assign:Parser[PEnv, Stmt] = for {
        x <- p_var
        _ <- p_spaces
        _ <- p_equal
        _ <- p_spaces
        e <- p_exp
        _ <- p_spaces
        _ <- p_semicolon
    } yield Assign(x, e)

    /**
      * Parsing a return statement
      *
      * @return
      */
    def p_ret:Parser[PEnv, Stmt] = for {
        _ <- p_returnKW
        _ <- p_spaces
        x <- p_var
        _ <- p_spaces
        _ <- p_semicolon
    } yield Ret(x)

    /**
      * Parsing an if-else statement
      *
      * @return
      */
    def p_ifelse:Parser[PEnv, Stmt] = for {
        _ <- p_ifKW
        _ <- p_spaces
        e <- p_exp
        _ <- p_spaces
        _ <- p_lbrace
        s1 <- p_stmts
        _ <- p_rbrace
        _ <- p_spaces 
        _ <- p_elseKW
        _ <- p_spaces
        _ <- p_lbrace
        s2 <- p_stmts
        _ <- p_rbrace
    } yield If(e, s1, s2)

    /**
      * Parsing a while statement
      *
      * @return
      */
    def p_while:Parser[PEnv, Stmt] = for {
        _ <- p_whileKW
        _ <- p_spaces
        e <- p_exp
        _ <- p_spaces
        _ <- p_lbrace
        s <- p_stmts
        _ <- p_rbrace
    } yield While(e, s)

    /** Lab 1 Task 1.1
      * parsing / skipping whitespaces
      *
      * @return
    */
    
    //fixme - fixed @jd 5th Nov
    // sat(callback_fn) -> returns Parser[E, T]
    // sat provides guard rails and error handling. Reference notes
    def p_space:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case WhiteSpace(_,_) => true
        case _ => false
    })   

    /* fixme - fixed @jd
    - I reference code in p_stmts for p_spaces
            def many[E, A, T](p: Parser[E, A])(using pe:ParserEnv[E,T]): Parser[E, List[A]]
    */
    def p_spaces:Parser[PEnv, List[LToken]] = {
        many(p_space)
    }

    /** Lab 1 Task 1.1 end */


    /** Lab 1 Task 1.2 
      * Parsing an expression
      * Note that 
      *   E ::= E Op E | X | C | (E) contains left recursion
      * @return
      */

    /*  fixme - fixed @jd 5th Nov
    
    Task 1.2
        1. apply the left-recursion elimination to generate a left-recursion-free equivalent grammar for the expression.
        
        Solution: We need to change the grammar bro
        Generic Fix formula:
        N :: = Nx|y where y terminates
        N ::= yN'
        N'::= xN' | eps
        After applying this formula
            Atom ::= X | C | (E)
            E    ::= Atom E'
            E'   ::= Op Atom E' | ε
            Op   ::= + | - | * | < | ==

        2. define the needed parser and sub parsers that parse the input using the left-recursion-free grammar.
            
            Solution:
                We will come up with a few sub parsers and use it inside a for-comprehension

        3. convert the resulted expression AST in the left-recursion-free grammar back to the AST in the left-recursion grammar.
            Reference notes on that LE term thingy
     */
    
    def p_exp:Parser[PEnv, Exp] = {
    
        /*
        New grammar for LE
            Atom ::= X | C | (E)
            E    ::= Atom E'
            E'   ::= Op Atom E' | eps
            Op   ::= + | - | * | < | ==
        */
        
        
        def p_paren: Parser[PEnv, Exp] = for {
            /*                
            This is for this specific case : (E) → ParenExp(E)
            for-comprehension explained:
                def map[B](f: A => B): Parser[E, B]
                we use for comprehension here
            */
            _ <- p_lparen
            _ <- p_spaces // @jd - when I referenced prof code, he seems to do this to remove any potential spaces. Look at above stmts
            e <- p_exp
            _ <- p_spaces
            _ <- p_rparen
            // @jd - Look into AST.scala - it has all the Enums definition. We definitely need to return the Enum
            // @jd - we only wanted to extract the e to form ParenExp
            // @jd the other _ <- statements uses .bind that acts as guardrails. Reference notes.
        } yield (ParenExp(e))

        
        def p_atom: Parser[PEnv, Exp] = {
            // Atom ::= X | C | (E)

            // p_var -> [PEnv, Var]            
            val p_v = for {
                v <- p_var
            } yield( VarExp(v))

            // p_const -> [Penv, Const]
            val p_c = for {
                c <- p_const
            } yield( ConstExp(c))
            choice(p_paren)(choice(p_v)(p_c))
        }

        
        def p_op: Parser[PEnv, LToken] ={
            // Follow this sequence from the .md file here 
            choice(p_plus) // Op ::= + | - | * | < | ==
                (choice(p_minus)
                    (choice(p_mult)
                        (choice(p_lthan)(p_dequal))
                    )
                )
        }

        
        // E    = Atom E'
        // E'   = op E' | eps
        def p_atom_exp_prime(head: Exp, rest:List[(LToken, Exp)]): Exp = {
            /*  
                rule2 : E'   ::= Op Atom E' | eps
                Left-associative: (((head op1 e1) op2 e2) op3 e3) ...     
                We need to break the main argument Exp into a List of tokens first
                    - and then we can run this function
                        - this function will return a final Exp which we will use inside the yield of a for-comprehension to return the Parser
            */
            
            rest.foldLeft(head) { (acc: Exp, pair: (LToken, Exp)) =>
                // head is the seed / accumulator. We will slowly extend it.
                val (tok, e) = pair
                tok match {
                    // Converting Lexer tokens into AST enums
                     // Sequence of Op ::= + | - | * | < | ==
                    case PlusSign(_)    => Plus(acc, e) // we dont care about srcLoc inside PlusSign(srcLoc)
                    case MinusSign(_)   => Minus(acc, e)
                    case AsterixSign(_) => Mult(acc, e)
                    case LThanSign(_)   => LThan(acc, e)
                    case DEqSign(_)     => DEqual(acc, e)
                    case _              => acc
                }
            }

        }

        // Combining rule 1 and 2 to get the Exp and then returning the parser
        // head + p_exp_prime
        for {
            head <- p_atom

            // rule 2 here E'   ::= Op Atom E' | eps     
            // we use many to recurssively call E'
            // we use attempt to backtrack. Otherwise we can't pass the last testcase
            tail <- many(attempt(for{ 
                // tail:Parser[E, List[A]]
                _ <- p_spaces
                op <- p_op
                _ <- p_spaces
                atom <- p_atom
                // desugars as p_op.flatMap(op=> p_atom.map(atom => op,atom))
            }yield(op, atom)))
        } yield(p_atom_exp_prime(head, tail))
        
    }

    //empty(ConstExp(IntConst(1))) 
    /** Lab 1 Task 1.2 end */
    
    /**
      * Parsing operator symbols
      *
      * @return
      */
    def p_plus:Parser[PEnv,LToken] = sat(ltoken => ltoken match {
        case PlusSign(_) => true 
        case _ => false
    })

    def p_minus:Parser[PEnv,LToken] = sat(ltoken => ltoken match {
        case MinusSign(_) => true 
        case _ => false
    })

    def p_mult:Parser[PEnv,LToken] = sat(ltoken => ltoken match {
        case AsterixSign(_) => true 
        case _ => false
    })

    def p_lthan:Parser[PEnv,LToken] = sat(ltoken => ltoken match {
        case LThanSign(_) => true 
        case _ => false
    })

    def p_dequal:Parser[PEnv,LToken] = sat(ltoken => ltoken match {
        case DEqSign(_) => true 
        case _ => false
    })

    def p_equal:Parser[PEnv,LToken] = sat(ltoken => ltoken match {
        case EqSign(_) => true 
        case _ => false
    })

    /**
      * Parsing a Variable
      *
      * @return
      */
    def p_var:Parser[PEnv, Var] = for {
        tok <- sat((ltoken:LToken) => ltoken match {
            case IdTok(src, v) => true
            case _ => false 
        })
        name <- someOrFail(tok)( t => t match {
            case IdTok(src, v) =>  Some(v)
            case _ => None
        })("error: expecting an identifier, but None is returned.") // this error should never occur.
    } yield Var(name)


    /**
      * Parsing a Constant
      *
      * @return
      */
    def p_const:Parser[PEnv, Const] = choice(choice(p_true)(p_false))(p_int)

    def p_true:Parser[PEnv, Const] = for {
        tok <- sat((ltoken:LToken) => ltoken match {
            case TrueKW(src) => true
            case _ => false 
        })
    } yield BoolConst(true)

    def p_false:Parser[PEnv, Const] = for {
        tok <- sat((ltoken:LToken) => ltoken match {
            case FalseKW(src) => true
            case _ => false 
        })
    } yield BoolConst(false)

    def p_int:Parser[PEnv, Const] = for {
        tok <- sat((ltoken:LToken) => ltoken match {
            case IntTok(src, v) => true
            case _ => false
        })
        i <- someOrFail(tok)( t => t match {
            case IntTok(src, v) =>  Some(v)
            case _ => None
        })("error: expecting an integer, but None is returned.") // this error should never occur.
    } yield IntConst(i)

    /**
      * Parsing keywords
      *
      * @return
      */
    def p_returnKW:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case RetKW(src) => true
        case _ => false
    })

    def p_ifKW:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case IfKW(src) => true
        case _ => false
    })

    def p_elseKW:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case ElseKW(src) => true
        case _ => false
    })

    def p_whileKW:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case WhileKW(src) => true
        case _ => false
    })



    /**
      * Parsing symbols
      */
    def p_lbrace:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case LBrace(src) => true
        case _ => false
    })

    def p_rbrace:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case RBrace(src) => true
        case _ => false
    })


    def p_lparen:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case LParen(src) => true
        case _ => false
    })

    def p_rparen:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case RParen(src) => true
        case _ => false
    })

    def p_semicolon:Parser[PEnv, LToken] = sat(ltoken => ltoken match {
        case SemiColon(src) => true
        case _ => false
    })



}