package sutd.compiler.simp.interpreter



import sutd.compiler.simp.syntax.AST.*


/**
  * the SIMP program interpreter by implementing the big step operational semantics
  */
object SimpInt {
    /**
      * the variable environment
      */
    type Delta = Map[Var, Const] 
    type ErrMsg = String
    import Exp.*
    /**
      * implementing the big step operational semantics Delta, e \Downarrow c
      *  the rules are partial function, hence we need an Either[ErrMsg,_] monad
      * @param dlt - the variable environment 
      * @param e   - the expression to be evaluated
      * @return either errror or the const
      */
    def evalExp(dlt:Delta, e:Exp):Either[ErrMsg, Const] = e match {
      case ConstExp(l) => Right(l) 
      case DEqual(e1, e2) => for {
        c1 <- evalExp(dlt, e1)
        c2 <- evalExp(dlt, e2)
        c3 <- eqConst(c1,c2)
      } yield c3 
      case LThan(e1, e2) => for {
        c1 <- evalExp(dlt, e1) 
        c2 <- evalExp(dlt, e2)
        c3 <- ltConst(c1, c2) 
      } yield c3
      case Minus(e1, e2) => for {
        c1 <- evalExp(dlt, e1) 
        c2 <- evalExp(dlt, e2)
        c3 <- minusConst(c1,c2)
      } yield c3
      case Mult(e1, e2) => for {
        c1 <- evalExp(dlt, e1) 
        c2 <- evalExp(dlt, e2)
        c3 <- multConst(c1,c2)
      } yield c3
      case Plus(e1, e2) => for {
        c1 <- evalExp(dlt, e1) 
        c2 <- evalExp(dlt, e2)
        c3 <- plusConst(c1,c2)
      } yield c3

      // Lab 2 Task 1.1
      // from syntax/AST.scala
      case VarExp(v) => dlt.get(v) match {
        case None    => Left(s"variable undefined")
        case Some(c) => Right(c)
      }
      case ParenExp(e1) => evalExp(dlt, e1)
      // Lab 2 Task 1.1 end
      // sbt compile "testOnly sutd.compiler.simp.TestSimpInt -- -z evalExp" 
    }

    import Stmt.* 
    import Const.*
    /**
      * implementing the big step operational semantics Delta, s \Downarrow Delta'
      *  the rules are partial function, hence we need an Either[ErrMsg,_] monad
      * @param dlt - the variable environment 
      * @param s   - the statement to be evaluated
      * @return either errror or the delta'      
      **/

    trait Evaluable[A] {
      def eval(dlt:Delta, a:A):Either[ErrMsg, Delta]
    }
    
    given evalMany[A](using i:Evaluable[A]):Evaluable[List[A]] = new Evaluable[List[A]] {
      def eval(dlt:Delta, ss:List[A]):Either[ErrMsg, Delta] = ss match {
        case Nil => Right(dlt) 
        // Lab 2 Task 1.2 
        case s :: rest =>
          i.eval(dlt,s) match {
            case Left(err) => Left(err)
            case Right(dlt1) => eval(dlt1, rest)
          }
        // Lab 2 Task 1.2 end
      }
    }

    given evalOne:Evaluable[Stmt] = new Evaluable[Stmt] {
      def eval(dlt:Delta, s:Stmt):Either[ErrMsg, Delta] = s match {
        case Nop => Right(dlt)
        case Assign(x, e) => for {
          c <- evalExp(dlt, e)
        } yield dlt + (x -> c)
        case If(cond, th, el) => for {
          c     <- evalExp(dlt, cond)
          dlt_2 <- c match {
            case IntConst(_) => Left("int expression found in the if condition position.")
            case BoolConst(b) if b => evalMany.eval(dlt, th)
            case BoolConst(b)      => evalMany.eval(dlt, el)  
          }
        } yield dlt_2
        case Ret(x) => Right(dlt)
        // Lab 2 Task 1.2 
        // syntax/AST.scala, implement While
        case While(cond, b) =>
          def loop(d: Delta): Either[ErrMsg, Delta] =
            evalExp(d, cond) match {
              case Left(err) => Left(err)
              case Right(IntConst(_)) => Left("int expression found in the while condition position")
              case Right(BoolConst(true)) =>
                evalMany.eval(d,b) match {
                  case Left(err) => Left(err)
                  case Right(d1) => loop(d1)
                }
              case Right(BoolConst(false)) => Right(d)
            }
          loop(dlt)
        // Lab 2 Task 1.2 end
      }
      //sbt "testOnly sutd.compiler.simp.TestSimpInt"

    }

    def eqConst(c1:Const, c2:Const):Either[ErrMsg, Const] = (c1,c2) match {
      case (IntConst(i1), IntConst(i2)) => Right(BoolConst(i1 == i2))
      case (BoolConst(b1), BoolConst(b2)) => Right(BoolConst(b1 == b2))
      case (_,_) => Left("different types of values are compared using ==")
    }

    def ltConst(c1:Const, c2:Const):Either[ErrMsg, Const] = (c1,c2) match {
      case (IntConst(i1), IntConst(i2)) => Right(BoolConst(i1 < i2))
      case (_,_) => Left("non int type of values are compared using <")
    }

    def minusConst(c1:Const, c2:Const):Either[ErrMsg, Const] = (c1,c2) match {
      case (IntConst(i1), IntConst(i2)) => Right(IntConst(i1 - i2))
      case (_,_) => Left("non int type of values are used with -")
    }

    def multConst(c1:Const, c2:Const):Either[ErrMsg, Const] = (c1,c2) match {
      case (IntConst(i1), IntConst(i2)) => Right(IntConst(i1 * i2))
      case (_,_) => Left("non int type of values are used with *")
    }

    def plusConst(c1:Const, c2:Const):Either[ErrMsg, Const] = (c1,c2) match {
      case (IntConst(i1), IntConst(i2)) => Right(IntConst(i1 + i2))
      case (_,_) => Left("non int type of values are used with +")
    }

    /**
      * The top level interpretor function for SIMP program
      *
      * @param p - the SIMP program
      * @param input - the integer input, might not be used
      * @return either an error or the const value result
      */
    def interpret(p:List[Stmt], input:Int):Either[ErrMsg, Const] = {
      val dlt:Map[Var,Const] = Map(Var("input") -> IntConst(input))
      getLastRetVar(p) match {
        case Left(err) => Left(err)
        case Right(Var(name)) => evalMany.eval(dlt, p) match {
          case Left(err) => Left(err)
          case Right(dlt1) => dlt1.get(Var(name)) match {
            case None => Left(s"undefined variable ${name}.")
            case Some(v) => Right(v)
          }
        }
      }
    }

    def getLastRetVar(p:List[Stmt]):Either[ErrMsg, Var] = p.reverse match {
      case Nil => Left("error: the program is empty")
      case (Ret(x)::_) => Right(x)
      case (_::_) => Left("error: the last statement of the SIMP program is not a return.")
    }

  }