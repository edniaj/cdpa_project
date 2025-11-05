package sutd.compiler.simp.syntax 

import sutd.compiler.simp.syntax.SrcLoc.*
import sutd.compiler.simp.monad.Monad.*
import sutd.compiler.simp.syntax.Parsec.*
/* @jiande - 5th nov'25 Lab 1
    We are designing SCALA COMPILEr that converts Simp code into IR (bunch of Scala enum instructions)
        - Prof has provided enums and functions. Use that
    Edit Parser.scala file 
*/
object Lexer {

    case class LEnv(tokens: List[Char], ln: Int, cl: Int)

    def eof(lenv:LEnv):Boolean = lenv match {
        case LEnv(Nil, _, _) => true
        case _ => false
    }

    given lenvParserEnv:ParserEnv[LEnv, Char] = new ParserEnv[LEnv, Char] {
        override def getTokens(env: LEnv): List[Char] = env match {
            case LEnv(toks, ln, cl) => toks
        }
        override def getCol(env: LEnv): Int = env match {
            case LEnv(toks, ln, cl) => cl
        }
        override def getLine(env: LEnv): Int = env match {
            case LEnv(toks, ln, cl) => ln
        }
        override def setTokens(ts: List[Char])(env: LEnv): LEnv = env match {
            case LEnv(toks, ln, cl) => LEnv(ts, ln, cl)
        }
        override def setLine(l: Int)(env: LEnv): LEnv = env match {
            case LEnv(toks, _, cl) => LEnv(toks, l, cl)
        }

        override def setCol(c: Int)(env: LEnv): LEnv = env match {
            case LEnv(toks, ln, _) => LEnv(toks, ln, c)
        }
    }


    val whitespaces = List('\t', '\r', '\n', ' ', '\f')


    type Id = String

    enum LToken {
        case EqSign(src:SrcLoc)
        case DEqSign(src:SrcLoc)
        case PlusSign(src:SrcLoc)
        case MinusSign(src:SrcLoc)
        case AsterixSign(src:SrcLoc)
        case FSlashSign(src:SrcLoc)

        case LThanSign(src:SrcLoc)
        // case GThanSign(src:SrcLoc)
        
        case LBrace(src:SrcLoc)
        case RBrace(src:SrcLoc)
        case LParen(src:SrcLoc)
        case RParen(src:SrcLoc)
        case SemiColon(src:SrcLoc)


        case RetKW(src:SrcLoc)
        case IfKW(src:SrcLoc)
        case ElseKW(src:SrcLoc)
        case WhileKW(src:SrcLoc)
        case NopKW(src:SrcLoc)
        case TrueKW(src:SrcLoc)
        case FalseKW(src:SrcLoc)

        case IdTok(src:SrcLoc, v:Id)
        case IntTok(src:SrcLoc, v:Int)
        case WhiteSpace(src:SrcLoc, c:Char)
    }

    import LToken.*

    def srcLoc(tok:LToken):SrcLoc = tok match {
        /* @jd 5th Nov'25
        Example of function call
            - If tok is PlusSign(SrcLoc(3, 10)), then srcLoc(tok) = SrcLoc(3, 10).
        
        SrcLoc is defined inside SrcLoc.scala
        object SrcLoc {
                case class SrcLoc(line:Int, col:Int)
            }
        
        I guess this fn main purpose is for error handling - "Syntax error at line 3, column 10" 
        
        */
        case EqSign(src) => src
        case DEqSign(src) => src
        case PlusSign(src) => src
        case MinusSign(src) => src
        case AsterixSign(src) => src
        case FSlashSign(src) => src

        case LThanSign(src) => src
        // case GThanSign(src) => src
        
        case LBrace(src) => src
        case RBrace(src) => src
        case LParen(src) => src
        case RParen(src) => src
        case SemiColon(src) => src

        case RetKW(src) => src
        case IfKW(src) => src
        case ElseKW(src) => src
        case WhileKW(src) => src
        case NopKW(src) => src    
        case TrueKW(src) => src
        case FalseKW(src) => src

        case IdTok(src, v) => src
        case IntTok(src, v) => src   

        case WhiteSpace(src, c) => src 
    }


    def l_EqSign(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '=')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (EqSign(SrcLoc(ln,cl)))

    // this must be wrapbe with attempt and comes before l_eqSign in a choice
    def l_DEqSign(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c1 <- sat((c:Char) => c == '=')
        c2 <- sat((c:Char) => c == '=')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (DEqSign(SrcLoc(ln,cl)))

    def l_PlusSign(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '+')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (PlusSign(SrcLoc(ln,cl)))

    def l_MinusSign(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '-')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (MinusSign(SrcLoc(ln,cl)))
    

    def l_AsterixSign(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '*')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (AsterixSign(SrcLoc(ln,cl)))


    def l_FSlashSign(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '/')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (FSlashSign(SrcLoc(ln,cl)))

    def  l_LThanSign(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '<')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (LThanSign(SrcLoc(ln,cl)))

    /*
    def  l_GThanSign(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '>')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (GThanSign(SrcLoc(ln,cl)))
    */

    def l_LBrace(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '{')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (LBrace(SrcLoc(ln,cl)))


    def l_RBrace(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '}')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (RBrace(SrcLoc(ln,cl)))

    def l_LParen(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '(')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (LParen(SrcLoc(ln,cl)))


    def l_RParen(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == ')')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (RParen(SrcLoc(ln,cl)))


    def l_SemiColon(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == ';')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (SemiColon(SrcLoc(ln,cl)))


    def string(s:String)(using pe:ParserEnv[LEnv, Char], m:MonadError[ParserM[LEnv], Error]):Parser[LEnv, List[Char]] = {
        val chars = s.toCharArray.toList
        def go(cs:List[Char]):Parser[LEnv,List[Char]] = cs match {
            case Nil => m.pure(Nil)
            case (x::xs) => for {
                t <- sat((c:Char) => c == x)
                ts <- go(xs)
            } yield (t::ts)
        }
        go(chars)
    }

    def l_RetKW(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        cs <- string("return")
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (RetKW(SrcLoc(ln,cl)))

    def l_IfKW(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        cs <- string("if")
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (IfKW(SrcLoc(ln,cl)))

    def l_ElseKW(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        cs <- string("else")
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (ElseKW(SrcLoc(ln,cl)))

    def l_WhileKW(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        cs <- string("while")
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (WhileKW(SrcLoc(ln,cl)))


    def l_NopKW(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        cs <- string("nop")
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (NopKW(SrcLoc(ln,cl)))

    def l_TrueKW(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        cs <- string("true")
                ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield TrueKW(SrcLoc(ln, cl))

    def l_FalseKW(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        cs <- string("false")
                ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield FalseKW(SrcLoc(ln, cl))

    def l_IntTok(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        _  <- lookAhead(sat((c:Char) => c.isDigit))
        cs <- everythingUntil((c:Char) => !c.isDigit)
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (IntTok(SrcLoc(ln,cl), cs.mkString.toInt))

    def l_IdTok(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        _  <- lookAhead(sat((c:Char) => c.isLetter))
        cs <- everythingUntil((c:Char) => !(c.isLetterOrDigit || c == '_'))
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (IdTok(SrcLoc(ln,cl), cs.mkString))

    def l_whitespace(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => whitespaces.contains(c))
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (WhiteSpace(SrcLoc(ln,cl), c))
    

    def lexOne:Parser[LEnv, LToken] = 
        choices(List(
            attempt(l_DEqSign),
            l_EqSign,
            l_PlusSign,
            l_MinusSign,
            l_AsterixSign,
            l_FSlashSign,
            l_LThanSign,
//            l_GThanSign,
            l_LBrace,
            l_RBrace,
            l_LParen,
            l_RParen,
            l_SemiColon,
            attempt(l_RetKW),
            attempt(l_IfKW),
            attempt(l_ElseKW),
            attempt(l_WhileKW),
            attempt(l_TrueKW),
            attempt(l_FalseKW),
            l_IntTok,
            l_IdTok
        ))(l_whitespace)
    
    def lex:Parser[LEnv, List[LToken]] = many(lexOne)

}