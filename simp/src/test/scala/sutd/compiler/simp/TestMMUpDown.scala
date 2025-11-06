package sutd.compiler.simp

import scala.language.adhocExtensions
import org.scalatest.funsuite 
import org.scalatest.matchers
import sutd.compiler.simp.syntax.AST.*
import sutd.compiler.simp.monad.StateT.{given, *}
import sutd.compiler.simp.ir.PseudoAssembly.*
import sutd.compiler.simp.ir.Util.{given, *}
import sutd.compiler.simp.ir.MMUpDown.*

class TestMMUpDown extends funsuite.AnyFunSuite {
    import Stmt.*, Var.*, Exp.*, Const.*
    import Instr.*, Opr.*

    test("test maximal munch v2 genExp: y + 1") {
        val exp1:Exp = Plus(VarExp(Var("y")), ConstExp(IntConst(1)))
        val expected = List((1,IPlus(Temp(AVar("var_1")),Temp(AVar("y")),IntLit(1))))
        genExp(exp1).run(StateInfo(1,"var", 1)) match {
            case Identity((st_, (opr,instrs))) => {
                // println(instrs)
                assert(expected == instrs)
            }
        }
    }

    test("test maximal munch v2 genExp: (x + 3) * (y - 5)") {
        val exp1:Exp = Mult(Plus(VarExp(Var("x")), ConstExp(IntConst(3))), Minus(VarExp(Var("y")), ConstExp(IntConst(5))))
        val expected = List(
            (1,IPlus(Temp(AVar("var_1")),Temp(AVar("x")),IntLit(3))), 
            (2,IMinus(Temp(AVar("var_2")),Temp(AVar("y")),IntLit(5))), 
            (3,IMult(Temp(AVar("var_3")),Temp(AVar("var_1")),Temp(AVar("var_2")))))
        genExp(exp1).run(StateInfo(1,"var", 1)) match {
            case Identity((st_, (opr,instrs))) => {
                // println(instrs)
                assert(expected == instrs)
            }
        }
    }


    // y = 1
    // x = y + 1
    test("test maximal munch v2: y = 1; x = y + 1") {
        val stmt1 = Assign(Var("y"), ConstExp(IntConst(1)))
        val stmt2 = Assign(Var("x"), Plus(VarExp(Var("y")), ConstExp(IntConst(1))))
        val expected = List(
            (1, IMove(Temp(AVar("y")),IntLit(1))), 
            (2, IPlus(Temp(AVar("var_1")),Temp(AVar("y")),IntLit(1))), 
            (3, IMove(Temp(AVar("x")),Temp(AVar("var_1")))))
        cogen(List(stmt1, stmt2)).run(StateInfo(1,"var", 1)) match {
            case Identity((st_, instrs)) => {
                // println(instrs)
                assert(expected == instrs)
            }
        }
    }    



    // z = (x + 3) * (y - 5)
    // return z
    test("test maximal munch v2: z = (x + 3) * (y - 5); return z") {
        val stmt1 = Assign(Var("z"), Mult(Plus(VarExp(Var("x")), ConstExp(IntConst(3))), Minus(VarExp(Var("y")), ConstExp(IntConst(5)))))
        val stmt2 = Ret(Var("z"))
        val expected = List(
            (1, IPlus(Temp(AVar("var_1")),Temp(AVar("x")),IntLit(3))), 
            (2, IMinus(Temp(AVar("var_2")),Temp(AVar("y")),IntLit(5))), 
            (3, IMult(Temp(AVar("var_3")),Temp(AVar("var_1")),Temp(AVar("var_2")))), 
            (4, IMove(Temp(AVar("z")),Temp(AVar("var_3")))), 
            (5, IMove(Regstr("_r_ret"),Temp(AVar("z")))), 
            (6, IRet)
        )
        cogen(List(stmt1, stmt2)).run(StateInfo(1,"var",1)) match {
            case Identity((st_, instrs)) => {
                // println(instrs)
                assert(expected == instrs)
            }
        }
    }

    // test("test maximal munch v2: while loop with sum") {
    //     /* x = 0
    //        y = 10
    //        i = 0
    //        while (i < y) {
    //           x = x + i
    //           i = i + 1
    //        }
    //        return x
    //     */
    //     val stmt1 = Assign(Var("x"), ConstExp(IntConst(0)))
    //     val stmt2 = Assign(Var("y"), ConstExp(IntConst(10)))
    //     val stmt3 = Assign(Var("i"), ConstExp(IntConst(0)))
    //     val stmt4 = While(LThan(VarExp(Var("i")), VarExp(Var("y"))), List(
    //         Assign(Var("x"), Plus(VarExp(Var("x")), VarExp(Var("i")))),
    //         Assign(Var("i"), Plus(VarExp(Var("i")), ConstExp(IntConst(1))))
    //     ))
    //     val stmt5 = Ret(Var("x"))

    //     val expected = List(
    //         (1,IMove(Temp(AVar("x")),IntLit(0))), 
    //         (2,IMove(Temp(AVar("y")),IntLit(10))), 
    //         (3,IMove(Temp(AVar("i")),IntLit(0))), 
    //         (4,ILThan(Temp(AVar("var_1")),Temp(AVar("i")),Temp(AVar("y")))), 
    //         (5,IIfNot(Temp(AVar("var_1")),11)), 
    //         (6,IPlus(Temp(AVar("var_2")),Temp(AVar("x")),Temp(AVar("i")))), 
    //         (7,IMove(Temp(AVar("x")),Temp(AVar("var_2")))), 
    //         (8,IPlus(Temp(AVar("var_3")),Temp(AVar("i")),IntLit(1))), 
    //         (9,IMove(Temp(AVar("i")),Temp(AVar("var_3")))), 
    //         (10,IGoto(4)), 
    //         (11,IMove(Regstr("_r_ret"),Temp(AVar("x")))), 
    //         (12,IRet))

        
    //     cogen(List(stmt1, stmt2, stmt3, stmt4, stmt5)).run(StateInfo(1,"var",1)) match {
    //         case Identity((st_, instrs)) => {
    //             // println(instrs)
    //             assert(expected == instrs)
    //         }
    //     }
    // }

    test("test maximal munch v2:" + """
    x = 0
    y = 10
    i = 0
    while (i < y) {
        x = x + i
        i = i + 1
    }
    return x
    """) {
        /* x = 0
           y = 10
           i = 0
           while (i < y) {
              x = x + i
              i = i + 1
           }
           return x
        */
        val stmt1 = Assign(Var("x"), ConstExp(IntConst(0)))
        val stmt2 = Assign(Var("y"), ConstExp(IntConst(10)))
        val stmt3 = Assign(Var("i"), ConstExp(IntConst(0)))
        val stmt4 = While(LThan(VarExp(Var("i")), VarExp(Var("y"))), List(
            Assign(Var("x"), Plus(VarExp(Var("x")), VarExp(Var("i")))),
            Assign(Var("i"), Plus(VarExp(Var("i")), ConstExp(IntConst(1))))
        ))
        val stmt5 = Ret(Var("x"))

        val expected = List(
            (1,IMove(Temp(AVar("x")),IntLit(0))), 
            (2,IMove(Temp(AVar("y")),IntLit(10))), 
            (3,IMove(Temp(AVar("i")),IntLit(0))), 
            (4,ILThan(Temp(AVar("var_1")),Temp(AVar("i")),Temp(AVar("y")))), 
            (5,IIfNot(Temp(AVar("var_1")),11)), 
            (6,IPlus(Temp(AVar("var_2")),Temp(AVar("x")),Temp(AVar("i")))), 
            (7,IMove(Temp(AVar("x")),Temp(AVar("var_2")))), 
            (8,IPlus(Temp(AVar("var_3")),Temp(AVar("i")),IntLit(1))), 
            (9,IMove(Temp(AVar("i")),Temp(AVar("var_3")))), 
            (10,IGoto(4)), 
            (11,IMove(Regstr("_r_ret"),Temp(AVar("x")))), 
            (12,IRet))

        
        cogen(List(stmt1, stmt2, stmt3, stmt4, stmt5)).run(StateInfo(1,"var",1)) match {
            case Identity((st_, instrs)) => {
                // println(instrs)
                assert(expected == instrs)
            }
        }
    }
}