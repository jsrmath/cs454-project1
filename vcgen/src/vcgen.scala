import scala.util.parsing.combinator._
import java.io.FileReader


object VCGen {

  /* Arithmetic expressions. */
  trait ArithExp

  case class Num(value: Int) extends ArithExp
  case class Var(name: String) extends ArithExp
  case class Read(name: String, ind: ArithExp) extends ArithExp
  case class Add(left: ArithExp, right: ArithExp) extends ArithExp
  case class Sub(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mul(left: ArithExp, right: ArithExp) extends ArithExp
  case class Div(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mod(left: ArithExp, right: ArithExp) extends ArithExp
  case class Parens(a: ArithExp) extends ArithExp
  case class WriteExp(x: String, ind: ArithExp, value: ArithExp) extends ArithExp


  /* Comparisons of arithmetic expressions. */
  type Comparison = Product3[ArithExp, String, ArithExp]


  /* Boolean expressions. */
  trait BoolExp

  case class BCmp(cmp: Comparison) extends BoolExp
  case class BNot(b: BoolExp) extends BoolExp
  case class BDisj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BConj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BParens(b: BoolExp) extends BoolExp

  /* Assetions, i.e. preconditions, postconditions, and invariants */
  trait Assertion

  case class AssnCmp(cmp: Comparison) extends Assertion
  case class AssnNot(c: Assertion) extends Assertion
  case class AssnDisj(left: Assertion, right: Assertion) extends Assertion
  case class AssnConj(left: Assertion, right: Assertion) extends Assertion
  case class AssnImp(left: Assertion, right: Assertion) extends Assertion
  case class AssnQuant(name: String, ids: List[String], exp: Assertion) extends Assertion
  case class AssnParens(c: Assertion) extends Assertion
  case class AssnTrue() extends Assertion
  case class AssnFalse() extends Assertion

  /* Statements and blocks. */
  trait Statement
  type Block = List[Statement]

  case class Assign(x: String, value: ArithExp) extends Statement
  case class Write(x: String, ind: ArithExp, value: ArithExp) extends Statement
  case class ParAssign(x1: String, x2: String, value1: ArithExp, value2: ArithExp) extends Statement
  case class If(cond: BoolExp, th: Block, el: Block) extends Statement
  case class While(cond: BoolExp, inv: Assertion, body: Block) extends Statement


  /* Complete programs. */
  type Program = Product4[String, Assertion, Assertion, Block]


  object ImpParser extends RegexParsers {
    /* General helpers. */
    def pvar  : Parser[String] = "\\p{Alpha}(\\p{Alnum}|_)*".r

    /* Parsing for ArithExp. */
    def num   : Parser[ArithExp] = "-?\\d+".r ^^ (s => Num(s.toInt))
    def atom  : Parser[ArithExp] =
      "(" ~> aexp <~ ")" |
      pvar ~ ("[" ~> aexp <~ "]") ^^ {case v ~ i => Read(v, i)} |
      num | pvar ^^ { Var(_) } |
      "-" ~> atom ^^ { Sub(Num(0), _) }
    def factor: Parser[ArithExp] =
      atom ~ rep("*" ~ atom | "/" ~ atom | "%" ~ atom) ^^ {
        case left ~ list => (left /: list) {
          case (left, "*" ~ right) => Mul(left, right)
          case (left, "/" ~ right) => Div(left, right)
          case (left, "%" ~ right) => Mod(left, right)
        }
      }
    def term  : Parser[ArithExp] =
      factor ~ rep("+" ~ factor | "-" ~ factor) ^^ {
        case left ~ list => (left /: list) {
          case (left, "+" ~ right) => Add(left, right)
          case (left, "-" ~ right) => Sub(left, right)
        }
      }
    def aexp  : Parser[ArithExp] = term

    /* Parsing for Comparison. */
    def comp  : Parser[Comparison] =
      aexp ~ ("=" | "<=" | ">=" | "<" | ">" | "!=") ~ aexp ^^ {
        case left ~ op ~ right => (left, op, right)
      }

    /* Parsing for BoolExp. */
    def batom : Parser[BoolExp] =
      "(" ~> bexp <~ ")" | comp ^^ { BCmp(_) } | "!" ~> batom ^^ { BNot(_) }
    def bconj : Parser[BoolExp] =
      batom ~ rep("&&" ~> batom) ^^ {
        case left ~ list => (left /: list) { BConj(_, _) }
      }
    def bdisj : Parser[BoolExp] =
      bconj ~ rep("||" ~> bconj) ^^ {
        case left ~ list => (left /: list) { BDisj(_, _) }
      }
    def bexp  : Parser[BoolExp] = bdisj

    /* Parsing for Assertion. */
    def aquant : Parser[Assertion] =
      ("forall" | "exists") ~ rep(pvar) ~ ("," ~> assn) ^^ { 
        case n ~ v ~ e => AssnQuant(n, v, e)
      }
    def aatom  : Parser[Assertion] =
      "(" ~> assn <~ ")" | comp ^^ { AssnCmp(_) } | "!" ~> aatom ^^ { AssnNot(_) } | aquant
    def aconj  : Parser[Assertion] =
      aatom ~ rep("&&" ~> aatom) ^^ {
        case left ~ list => (left /: list) { AssnConj(_, _) }
      }
    def adisj  : Parser[Assertion] =
      aconj ~ rep("||" ~> aconj) ^^ {
        case left ~ list => (left /: list) { AssnDisj(_, _) }
      }
    def aimp   : Parser[Assertion] =
      adisj ~ rep("==>" ~> adisj) ^^ {
        case left ~ list => (left /: list) { AssnImp(_, _) }
      }
    def assn   : Parser[Assertion] = aimp

    def assnlist(str: String) : Parser[Assertion] =
      rep(str ~> assn) ^^ { 
        case first :: rest => (first /: rest) { AssnConj(_, _) }
        case Nil => AssnTrue()
      }

    /* Parsing for Statement and Block. */
    def block : Parser[Block] = rep(stmt)
    def stmt  : Parser[Statement] =
      pvar ~ ("[" ~> aexp <~ "]") ~ (":=" ~> aexp <~ ";") ^^ {
        case v ~ i ~ e => Write(v, i, e)
      } |
      (pvar <~ ":=") ~ (aexp <~ ";") ^^ {
        case v ~ e => Assign(v, e)
      } |
      (pvar <~ ",") ~ (pvar <~ ":=") ~ (aexp <~ ",") ~ (aexp <~ ";") ^^ {
        case v1 ~ v2 ~ e1 ~ e2 => ParAssign(v1, v2, e1, e2)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "else") ~ (block <~ "end") ^^ {
        case c ~ t ~ e => If(c, t, e)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "end") ^^ {
        case c ~ t => If(c, t, Nil)
      } |
      ("while" ~> bexp) ~ (assnlist("inv") <~ "do") ~ (block <~ "end") ^^ {
        case c ~ i ~ b => While(c, i, b)
      }

    /* Parsing for Program. */
    def prog      : Parser[Program] =
      ("program" ~> pvar) ~ assnlist("pre") ~ assnlist("post") ~ ("is" ~> block <~ "end") ^^ {
        case n ~ pre ~ post ~ b => (n, pre, post, b)
      }
  }

  /* Guarded Commands */
  trait GuardedCommand
  type GCProgram = List[GuardedCommand]

  case class GCAssume(assn: Assertion) extends GuardedCommand
  case class GCAssert(assn: Assertion) extends GuardedCommand
  case class GCHavoc(id: Var) extends GuardedCommand
  case class GCBranch(left: GCProgram, right: GCProgram) extends GuardedCommand

  var tmpCount = -1

  def getFreshVariable(): String = {
    tmpCount += 1
    "_tmp" + tmpCount
  }

  def replaceVarInExp(exp: ArithExp, oldVar: String, newVar: String): ArithExp = {
    exp match {
      case Num(value) => Num(value)
      case Var(name) => Var(if (name == oldVar) newVar else name)
      case Read(name, ind) => Read(name, replaceVarInExp(ind, oldVar, newVar))
      case Add(left, right) => Add(replaceVarInExp(left, oldVar, newVar), replaceVarInExp(right, oldVar, newVar))
      case Sub(left, right) => Sub(replaceVarInExp(left, oldVar, newVar), replaceVarInExp(right, oldVar, newVar))
      case Mul(left, right) => Mul(replaceVarInExp(left, oldVar, newVar), replaceVarInExp(right, oldVar, newVar))
      case Div(left, right) => Div(replaceVarInExp(left, oldVar, newVar), replaceVarInExp(right, oldVar, newVar))
      case Mod(left, right) => Mod(replaceVarInExp(left, oldVar, newVar), replaceVarInExp(right, oldVar, newVar))
      case Parens(a) => Parens(replaceVarInExp(a, oldVar, newVar))
      case WriteExp(a, i, v) =>
        WriteExp(if (a == oldVar) newVar else a, replaceVarInExp(i, oldVar, newVar), replaceVarInExp(v, oldVar, newVar))
    }
  }

  def replaceVarInAssertion(assn: Assertion, oldVar: String, newVar: String): Assertion = {
    assn match {
      case AssnCmp((a1, s, a2))
        => AssnCmp((replaceVarInExp(a1, oldVar, newVar), s, replaceVarInExp(a2, oldVar, newVar)))
      case AssnNot(assn) => AssnNot(replaceVarInAssertion(assn, oldVar, newVar))
      case AssnDisj(left, right)
        => AssnDisj(replaceVarInAssertion(left, oldVar, newVar), replaceVarInAssertion(right, oldVar, newVar))
      case AssnConj(left, right)
        => AssnConj(replaceVarInAssertion(left, oldVar, newVar), replaceVarInAssertion(right, oldVar, newVar))
      case AssnImp(left, right)
        => AssnImp(replaceVarInAssertion(left, oldVar, newVar), replaceVarInAssertion(right, oldVar, newVar))
      case AssnQuant(name, ids, assn)
        => AssnQuant(name, ids, replaceVarInAssertion(assn, oldVar, newVar))
      case AssnParens(assn) => AssnParens(replaceVarInAssertion(assn, oldVar, newVar))
      case x => x
    }
  }

  def getModifiedVars(block: Block): List[String] = {
    val empty: List[String] = List()
    block.foldLeft(empty) { (vars: List[String], s: Statement) => s match {
      case Assign(x, _) => x :: vars
      case Write(a, _, _) => a :: vars
      case ParAssign(x1, x2, _, _) => x1 :: x2 :: vars
      case If(_, th, el) => getModifiedVars(th) ++ getModifiedVars(el) ++ vars
      case While(_, _, body) => getModifiedVars(body) ++ vars
    }}
  }

  def assnFromBool(bool: BoolExp): Assertion = {
    bool match {
      case BCmp(cmp) => AssnCmp(cmp)
      case BNot(b) => AssnNot(assnFromBool(b))
      case BDisj(left, right) => AssnDisj(assnFromBool(left), assnFromBool(right))
      case BConj(left, right) => AssnConj(assnFromBool(left), assnFromBool(right))
      case BParens(b) => AssnParens(assnFromBool(b))
    }
  }

  def makeGuardedCommandFromAssign(x: String, e: ArithExp): GCProgram = {
    val tmp = getFreshVariable()
    List(
      GCAssume(AssnCmp((Var(tmp), "=", Var(x)))),
      GCHavoc(Var(x)),
      GCAssume(AssnCmp((Var(x), "=", replaceVarInExp(e, x, tmp))))
    )
  }

  def makeGuardedCommandFromWrite(x: String, ind: ArithExp, value: ArithExp): GCProgram = {
    makeGuardedCommandFromAssign(x, WriteExp(x, ind, value))
  }

  def makeGuardedCommandFromParAssign(x1: String, x2: String, e1: ArithExp, e2: ArithExp): GCProgram = {
    val tmp1 = getFreshVariable()
    val tmp2 = getFreshVariable()
    List(
      GCAssume(AssnCmp((Var(tmp1), "=", Var(x1)))),
      GCAssume(AssnCmp((Var(tmp2), "=", Var(x2)))),
      GCHavoc(Var(x1)),
      GCHavoc(Var(x2)),
      GCAssume(AssnCmp((Var(x1), "=", replaceVarInExp(replaceVarInExp(e1, x1, tmp1), x2, tmp2)))),
      GCAssume(AssnCmp((Var(x2), "=", replaceVarInExp(replaceVarInExp(e2, x1, tmp1), x2, tmp2))))
    )
  }

  def makeGuardedCommandFromIf(cond: BoolExp, th: Block, el: Block): GCProgram = {
    val assnCond = assnFromBool(cond)
    List(GCBranch(
      GCAssume(assnCond) :: makeGuardedCommand(th),
      GCAssume(AssnNot(assnCond)) :: makeGuardedCommand(el)
    ))
  }

  def makeGuardedCommandFromWhile(cond: BoolExp, inv: Assertion, body: Block): GCProgram = {
    val modifiedVars = getModifiedVars(body)
    val assnCond = assnFromBool(cond)
    GCAssert(inv) ::
    modifiedVars.map((x) => GCHavoc(Var(x))) ++
    List(
      GCAssume(inv),
      GCBranch(
        (
          GCAssume(assnCond) ::
          makeGuardedCommand(body) ++
          List(
            GCAssert(inv),
            GCAssume(AssnFalse())
          )
        ),
        List(
          GCAssume(AssnNot(assnCond))
        )
      )
    )
  }

  def makeGuardedCommandFromStatement(statement: Statement): GCProgram = {
    statement match {
      case Assign(x, value) => makeGuardedCommandFromAssign(x, value)
      case Write(x, ind, value) => makeGuardedCommandFromWrite(x, ind, value)
      case ParAssign(x1, x2, value1, value2) => makeGuardedCommandFromParAssign(x1, x2, value1, value2)
      case If(cond, th, el) => makeGuardedCommandFromIf(cond, th, el)
      case While(cond, inv, body) => makeGuardedCommandFromWhile(cond, inv, body)
    }
  }

  def makeGuardedCommand(b: Block): GCProgram = {
    b.toList.flatMap(makeGuardedCommandFromStatement)
  }

  def findWeakestPrecondition(p: GCProgram, b: Assertion): Assertion = {
    p.foldRight(b) { (c: GuardedCommand, b: Assertion) => c match {
      case GCAssume(assn) => AssnImp(assn, b)
      case GCAssert(assn) => AssnConj(assn, b)
      case GCHavoc(Var(x)) => replaceVarInAssertion(b, x, getFreshVariable())
      case GCBranch(p1, p2) => AssnConj(findWeakestPrecondition(p1, b), findWeakestPrecondition(p2, b))
    }}
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._;
    val p = parseAll(prog, reader).get
    val gc = makeGuardedCommand(p._4)
    val ch = GCAssume(p._2) :: gc ++ List(GCAssert(p._3))
    val wp = findWeakestPrecondition(ch, AssnTrue())
    println(wp)
  }
}
