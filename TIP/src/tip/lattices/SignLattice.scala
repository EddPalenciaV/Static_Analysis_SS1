package tip.lattices

/** An element of the sign lattice.
  */
object SignElement extends Enumeration {
  val Pos, Neg, Zero = Value
}

/** The sign lattice.
  */
object SignLattice extends FlatLattice[SignElement.Value] with LatticeWithOps {

  import SignElement._

  private val signValues: Map[Element, Int] = Map(
    Bot -> 0,
    FlatEl(Zero) -> 1,
    FlatEl(Neg) -> 2,
    FlatEl(Pos) -> 3,
    Top -> 4
  )

  private def lookup(op: List[List[Element]], x: Element, y: Element): Element =
    op(signValues(x))(signValues(y))

  private val absPlus: List[List[Element]] =
    List(
      // List(Bot, Bot, Bot, Bot, Bot),
      // List(Bot, Zero, Neg, Pos, Top),
      // List(Bot, Neg, Neg, Top, Top),
      // List(Bot, Pos, Top, Pos, Top),
      // List(Bot, Top, Top, Top, Top)

      List(Bot, Bot, Bot, Bot, Bot),
      List(Bot, Zero, Neg, Pos, Top),
      List(Bot, Neg, Neg, Top, Top),
      List(Bot, Pos, Top, Pos, Top),
      List(Bot, Top, Top, Neg, Neg) // NOT MONOTONIC
    )

  private val absMinus: List[List[Element]] =
    List(
      List(Bot, Bot, Bot, Bot, Bot),
      List(Bot, Zero, Pos, Neg, Top),
      List(Bot, Neg, Top, Neg, Top),
      List(Bot, Pos, Pos, Top, Top),
      List(Bot, Top, Top, Top, Top)
    )

  private val absTimes: List[List[Element]] =
    List(
      List(Bot, Bot, Bot, Bot, Bot),
      List(Bot, Zero, Zero, Zero, Zero),
      List(Bot, Zero, Pos, Neg, Top),
      List(Bot, Zero, Neg, Pos, Top),
      List(Bot, Zero, Top, Top, Top)
    )

  private val absDivide: List[List[Element]] =
    List(
      List(Bot, Bot, Bot, Bot, Bot),
      List(Bot, Bot, Zero, Zero, Top),
      List(Bot, Bot, Top, Top, Top),
      List(Bot, Bot, Top, Top, Top),
      List(Bot, Bot, Top, Top, Top)
    )

  private val absGt: List[List[Element]] =
    List(
      // List(Bot, Bot, Bot, Bot, Bot),
      // List(Bot, Zero, Pos, Zero, Top),
      // List(Bot, Zero, Top, Zero, Top),
      // List(Bot, Pos, Pos, Top, Top),
      // List(Bot, Top, Top, Top, Top)

      List(Bot, Bot, Bot, Bot, Bot),
      List(Bot, Zero, Pos, Zero, Top),
      List(Bot, Zero, Top, Zero, Top),
      List(Bot, Pos, Pos, Top, Top),
      List(Bot, Top, Top, Neg, Neg) // NOT MONOTONIC
    )

  private val absEq: List[List[Element]] =
    List(
      // List(Bot, Bot, Bot, Bot, Bot),
      // List(Bot, Pos, Zero, Zero, Top),
      // List(Bot, Zero, Top, Zero, Top),
      // List(Bot, Zero, Zero, Top, Top),
      // List(Bot, Top, Top, Top, Top)

      List(Bot, Bot, Bot, Bot, Bot),
      List(Bot, Pos, Zero, Zero, Top),
      List(Bot, Zero, Top, Zero, Top),
      List(Bot, Zero, Zero, Top, Top),
      List(Bot, Top, Top, Neg, Neg) // NOT MONOTONIC
    )

  def num(i: Int): Element =
    if (i == 0)
      Zero
    else if (i > 0)
      Pos
    else
      Neg

  def plus(a: Element, b: Element): Element = lookup(absPlus, a, b)

  def minus(a: Element, b: Element): Element = lookup(absMinus, a, b)

  def times(a: Element, b: Element): Element = lookup(absTimes, a, b)

  def div(a: Element, b: Element): Element = lookup(absDivide, a, b)

  def eqq(a: Element, b: Element): Element = lookup(absEq, a, b)

  def gt(a: Element, b: Element): Element = lookup(absGt, a, b)

  def plus10(a: Int): Int = (a + 10)

  //Monotonic
  def plus10Abstract(a: Element): Element = plus(a, Pos)
  //NOT Monotonic
  //def plus10Abstract(a: Element): Element = (if (a == Top) Bot else a)

  def checkMonotone(name: String, op: (Element, Element) => Element): Unit = {
  // your loops from Steps 2–3, using op(...) instead of plus(...)
    println(s"Now Testing ~$name~ case...")
    for (a <- signValues.keys; b <- signValues.keys; c <- signValues.keys) {
        if (leq(a, b)) {
          if (!leq(op(a, c), op(b, c))) {   // hint: when is f(a, c) ⊑ f(b, c) violated?
            println(s"Function ~$name~ NOT monotone in 1st arg: $a <= $b but op($a, $c) = ${op(a, c)} and op($b, $c) = ${op(b, c)}")
            // return
          }
          if (!leq(op(c, a), op(c, b))) {
            println(s"Function ~$name~ NOT monotone in 2nd arg: $a <= $b but op($c, $a) = ${op(c, a)} and op($c, $b) = ${op(c, b)}")
            // return          
          }
        }
      }
      // println("still MONOTONIC...")
  }


  def main(args: Array[String]): Unit = {   

    // INSTEAD of the long code below, use checkMonotone(name,op)
    checkMonotone("plus", plus)
    checkMonotone("gt", gt)
    checkMonotone("eqq", eqq)

    println("Testing plus10Abstract...")
    for (a <- signValues.keys) {
      val out = plus10Abstract(a)
      println(s"input $a gives output $out")
    }
    for (a <- signValues.keys; b <- signValues.keys if leq(a, b)) {
      if (!leq(plus10Abstract(a), plus10Abstract(b))){
        println(s"Is NOT monotonic because: ($a) <= ($b) but f(${plus10Abstract(a)}) > f(${plus10Abstract(b)})")
        // return
      }
    }
    // println("It IS MONOTONIC!")
    
    // println("Now Testing Plus + case...")
    // for (a <- signValues.keys; b <- signValues.keys; c <- signValues.keys) {
    //   if (leq(a, b)) {
    //     if (!leq(plus(a, c), plus(b, c))) {   // hint: when is f(a, c) ⊑ f(b, c) violated?
    //       println(s"Function ~plus~ NOT monotone in 1st arg: $a <= $b but plus($a, $c) = ${plus(a, c)} and plus($b, $c) = ${plus(b, c)}")
    //       return
    //     }
    //     if (!leq(plus(c, a), plus(c, b))) {
    //       println(s"Function ~plus~ NOT monotone in 2nd arg: $a <= $b but plus($c, $a) = ${plus(c, a)} and plus($c, $b) = ${plus(c, b)}")
    //       return          
    //     }
    //   }
    // }
    // println("still MONOTONIC...")

    // println("Now Testing Greater > case...")
    // for (a <- signValues.keys; b <- signValues.keys; c <- signValues.keys) {
    //   if (leq(a, b)) {
    //     if (!leq(gt(a, c), gt(b, c))) {   // hint: when is f(a, c) ⊑ f(b, c) violated?
    //       println(s"Function ~gt~ NOT monotone in 1st arg: $a <= $b but plus($a, $c) = ${gt(a, c)} and plus($b, $c) = ${gt(b, c)}")
    //       return
    //     }
    //     if (!leq(gt(c, a), gt(c, b))) {
    //       println(s"Function ~gt~ NOT monotone in 2nd arg: $a <= $b but plus($c, $a) = ${gt(c, a)} and plus($c, $b) = ${gt(c, b)}")
    //       return          
    //     }
    //   }
    // }
    // println("still MONOTONIC...")

    // println("Now Testing Equal == case...")
    // for (a <- signValues.keys; b <- signValues.keys; c <- signValues.keys) {
    //   if (leq(a, b)) {
    //     if (!leq(eqq(a, c), eqq(b, c))) {   // hint: when is f(a, c) ⊑ f(b, c) violated?
    //       println(s"Function ~eqq~ NOT monotone in 1st arg: $a <= $b but plus($a, $c) = ${eqq(a, c)} and plus($b, $c) = ${eqq(b, c)}")
    //       return
    //     }
    //     if (!leq(eqq(c, a), eqq(c, b))) {
    //       println(s"Function ~eqq~ NOT monotone in 2nd arg: $a <= $b but plus($c, $a) = ${eqq(c, a)} and plus($c, $b) = ${eqq(c, b)}")
    //       return          
    //     }
    //   }
    // }
    // println("still MONOTONIC...")

  }
}
