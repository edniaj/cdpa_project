package sutd.compiler.simp.ir


import sutd.compiler.simp.monad.Functor.*
import sutd.compiler.simp.monad.Applicative.*
import sutd.compiler.simp.monad.Monad.*
import sutd.compiler.simp.monad.StateT.*
import sutd.compiler.simp.syntax.AST.*
import sutd.compiler.simp.ir.PseudoAssembly.*
import sutd.compiler.simp.ir.Util.*

/* @jd 6th Nov 2025
    
    We are converting SIMP AST (Exp, Stmt) into PseudoAssembly (Instr, Opr).
        genExp(E) : ( ê:Opr , ě: List[(Label,Instr)] ) where ê is operand and  ě is list of instr to compute the operand
    
    Reference PseudoAssembly.scala for 
        1. enum Instr
        2. enum Opr
*/

object MMUpDown {
    import Stmt.*
    import Var.*
    import Exp.*
    import Const.*
    import AVar.* 
    import Instr.*
    import Opr.*
    

    type UpE = Opr
    type DownE = List[Instr]
    
    // genExp(E) returns ( ê:Opr , ě: List[(Label,Instr)] ) where ê is operand and  ě is list of instr to compute the operand
    def genExp(e:Exp)(using me:StateCogenMonad[StateInfo]):CogenState[(Opr, List[(Label,Instr)])] = e match {
        // GE(c) |- (c, [])      (Const)
        case ConstExp(IntConst(v)) => me.pure((IntLit(v), Nil))
        // true into 1, false into 0
        case ConstExp(BoolConst(b)) if b => me.pure((IntLit(1), Nil))
        case ConstExp(BoolConst(b))      => me.pure((IntLit(0), Nil))
        // GE(X) |- (X, [])      (Var)
        case VarExp(v) => {
            val av = var2AVar(v) 
            me.pure((Temp(av), Nil))
        }
        /*
         GE(e) |- (up_e, down_e)
        ------------------------- (Paren)
         GE((e)) |- (up_e, down_e)
        */ 
        case ParenExp(e) => genExp(e)

        // Lab 1 Task 2.1 
        /*
         GE(e1) |- (up_e1, down_e1)
         GE(e2) |- (up_e2, down_e2)
         X is a fresh var
         L is a fresh label
        --------------------------------------------------------------------- (Op)
         GE(e1 op e2) |- (X, down_e1 ++ down_e2 ++ [L:X <- up_e1 op up_e2])
         
        We need to implement this thingy above into our case
        */ 
        
        // fixme - fixed @Jd 6th Nov'25
        // plus minus mult dequal lthan
        case Plus(e1,e2) => for { 
            // u means e up ê, d means e down ě
            (u1, d1) <- genExp(e1) // CogenState[(Opr, List[(Label,Instr)])]
            (u2,d2) <- genExp(e2) // CogenState[(Opr, List[(Label,Instr)])]
            tmp <- newTemp // CogenState[Opr]
            lbl <- newLabel // CogenState[Label]
            /* this desugars to 
                genExp(e1).flatMap { case (u1, d1) =>
                    genExp(e2).flatMap { case (u2, d2) =>
                        newTemp.flatMap { tmp =>
                            newLabel.map { lbl =>
                                val dest  = Temp(tmp)
                                val instr = IPlus(dest, u1, u2)
                                (dest, d1 ++ d2 ++ List((lbl, instr)))
                            }
                        }
                    }
                }                        
            */
            } yield({ // this will return a CogenState(dest, ě1 ++ ě2 ++ List[(lbl, instr)])
                val dest = tmp
                val instr = IPlus(dest, u1, u2)
                (dest, d1 ++ d2 ++ List((lbl, instr)))
            })

        case Minus(e1,e2) => for { 
            // u means e up ê, d means e down ě
            (u1, d1) <- genExp(e1) // CogenState[(Opr, List[(Label,Instr)])]
            (u2,d2) <- genExp(e2) // CogenState[(Opr, List[(Label,Instr)])]
            tmp <- newTemp // CogenState[Opr]
            lbl <- newLabel // CogenState[Label]

            } yield({ // this will return a CogenState(dest, ě1 ++ ě2 ++ List[(lbl, instr)])
                val dest = tmp
                val instr = IMinus(dest, u1, u2)
                (dest, d1 ++ d2 ++ List((lbl, instr)))
            })

        case Mult(e1,e2) => for { 
            // u means e up ê, d means e down ě
            (u1, d1) <- genExp(e1) // CogenState[(Opr, List[(Label,Instr)])]
            (u2,d2) <- genExp(e2) // CogenState[(Opr, List[(Label,Instr)])]
            tmp <- newTemp // CogenState[Opr]
            lbl <- newLabel // CogenState[Label]

            } yield({ // this will return a CogenState(dest, ě1 ++ ě2 ++ List[(lbl, instr)])
                val dest = tmp
                val instr = IMult(dest, u1, u2)
                (dest, d1 ++ d2 ++ List((lbl, instr)))
            })

        case DEqual(e1,e2) => for { 
            // u means e up ê, d means e down ě
            (u1, d1) <- genExp(e1) // CogenState[(Opr, List[(Label,Instr)])]
            (u2,d2) <- genExp(e2) // CogenState[(Opr, List[(Label,Instr)])]
            tmp <- newTemp // CogenState[Opr]
            lbl <- newLabel // CogenState[Label]

            } yield({ // this will return a CogenState(dest, ě1 ++ ě2 ++ List[(lbl, instr)])
                val dest = tmp
                val instr = IDEqual(dest, u1, u2)
                (dest, d1 ++ d2 ++ List((lbl, instr)))
            })
        case LThan(e1,e2) => for { 
            // u means e up ê, d means e down ě
            (u1, d1) <- genExp(e1) // CogenState[(Opr, List[(Label,Instr)])]
            (u2,d2) <- genExp(e2) // CogenState[(Opr, List[(Label,Instr)])]
            tmp <- newTemp // CogenState[Opr]
            lbl <- newLabel // CogenState[Label]
            } yield({ // this will return a CogenState(dest, ě1 ++ ě2 ++ List[(lbl, instr)])
                val dest = tmp
                val instr = ILThan(dest, u1, u2)
                (dest, d1 ++ d2 ++ List((lbl, instr)))
            })
        // Lab 1 Task 2.1 end
    }

    // convert statement into List of Instructions
    def cogen(s:Stmt):CogenState[List[(Label,Instr)]] = s match {
        case Nop => StateT{ st => Identity((st, List())) } 
        /*
        GE(e) |- (up_e, down_e)
        L is a new label
        -------------------------------------- (Assign)
        G(X = e) |- down_e ++ [ L: X <- up_e]
        */ 
        case Assign(v, e) => for {
            (u, d) <- genExp(e)
            lbl    <- newLabel
        } yield { 
            val av = var2AVar(v)
            val i = IMove(Temp(av), u) // @jd - Instruction enum
            (d ++ List((lbl,i)))
        }
        /*
        GE(x) |- (up_e, down_e)
        L1 and L2 are new labels
        ---------------------------------------------------- (Return) 
        G(return x) |-  down_e ++ [ L1: R_ret <- up_e, L2: IReturn ]
        */
        case Ret(x) => for {
            (u, d) <- genExp(VarExp(x))
            lbl1   <- newLabel
            lbl2   <- newLabel
        } yield {
            val r_ret = Regstr("_r_ret")
            val i = IMove(r_ret, u)
            d ++ List((lbl1, i), (lbl2, IRet))
        }
        /*
        GE(cond) |- (up_cond, down_cond)
        LIf is a fresh label
        
        G(thn) |- instrs2
        LEndThen is a fresh label

        LElse is the next label (w/o incr)

        G(els) |- instrs3
        LEndElse is a fresh label

        LEndIf is the next label (w/o incr)
        instrs1 = [LIf: ifn up_cond goto LElse] 
        instrs2' = instrs2 ++ [LEndThen: goto LEndIf] 
        instrs3' = instrs3 ++ [LEndElse: goto LEndIf]
        ---------------------------------------------------- (If)
        G(if cond {thn} else {els}) |- down_cond ++ instrs1 ++ instrs2' ++ instrs3' 
        */
        case If(cond, thn, els) => for {
            (cond_u, cond_d) <- genExp(cond) 
            lblIf            <- newLabel 

            instrs2          <- cogen(thn)
            lblEThen         <- newLabel

            lblElse          <- chkNextLabel

            instrs3          <- cogen(els)
            lblEElse         <- newLabel

            lblEIf           <- chkNextLabel
            instrs1          = List((lblIf, IIfNot(cond_u, lblElse)))
            instrs2a         = instrs2 ++ List((lblEThen, IGoto(lblEIf)))
            instrs3a         = instrs3 ++ List((lblEElse, IGoto(lblEIf)))
        } yield cond_d ++ instrs1 ++ instrs2a ++ instrs3a
        // Lab 1 Task 2.2 
        /*
        1. LBWhile is the next label (w/o incr) 
        GE(cond) |- (up_cond, down_cond)

        2. LWhileCondJ is a fresh label
        G(body) |- instrs2 
        LEndBody is a fresh label
        
        3. LEndWhile is the next label (w/o incr)

        instrs1 = [LWhileCondJ: ifn up_cond goto LEndWhile] 
        instrs2' = instrs2 ++ [ LEndBody: goto LBWhile ]
        --------------------------------------------------------- (While)
        G(while cond {body}) |- down_cond ++ instrs1 ++ instrs2'

        @jd 6th Nov'25 - You can reference MaximalMunch.scala and see how they handle case While(cond,body). 
            - its very similar except we don't use temp. v2 is more efficient - reference Wk6 notes
        */

        // fixme - fixed @jd 6th Nov'25
        case While(cond, body) => for {
            // 1. LBWhile is the next label (w/o incr) 
            // GE(cond) |- (up_cond, down_cond)
            lblBWhile <- chkNextLabel

            // GE(cond) ⊢ (up_cond, down_cond)
            (uCond, dCond) <- genExp(cond)
                        
            // 2. LWhileCondJ is a fresh label
            lblWhileCondJ <- newLabel
            // G(body) |- instrs2
            instrsBody <- cogen(body) // this is a statemenet
            // LEndBody is a fresh label
            lblEndBody <- newLabel

            // 3. LEndWhile is the next label (w/o incr)    
            lblEndWhile <- chkNextLabel

        } yield({
            // instrs1 = [LWhileCondJ: ifn up_cond goto LEndWhile] 
            val instrs1 = List((lblWhileCondJ, IIfNot(uCond, lblEndWhile)))
            // instrs2' = instrs2 ++ [ LEndBody: goto LBWhile ]
            val instrs2p = instrsBody ++ List((lblEndBody, IGoto(lblBWhile)))
            dCond ++ instrs1 ++ instrs2p

            // @jd 6th Nov'25 - sidenote, you can put instrs1 and instrs2p inside the last flatMap. But I prefer to throw everyth inside the .map
        })
        // Lab 1 Task 2.2 end
    }


    /*
     for i in {1,n}    G(stmt_i) |- instrs_i
    -------------------------------------------------------- (Sequence)
     G(stmt_1,...,stmt_n) |- instrs_1 ++ ... ++  instrs_n
    */

    def cogen(l:List[Stmt]):CogenState[List[(Label,Instr)]] = for {
        ll <- traverse( (stmt:Stmt) => cogen(stmt), l)
    } yield ll.flatten
}