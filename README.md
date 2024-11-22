Not really usable as a fully fledged SMT solver right now.
Mainly just a collection of the various algorithms used in SMT solvers, implemented in Haskell:

* SAT solving
  * [x] [Davis–Putnam–Logemann–Loveland (DPLL)](/src/SAT/DPLL.hs)
  * [x] [Conflict Driven Clause Learning (CDCL)](/src/SAT/CDCL.hs)
* Uninterpreted Functions
  * [x] [Congruence Closure](/src/Theory/UninterpretedFunctions.hs)
* Linear Arithmatic
  * [x] [Simplex Method](/src/Theory/LinearArithmatic/Simplex.hs)
  * [x] [Fourier-Motzkin](/src/Theory/LinearArithmatic/FourierMotzkin.hs)
  * [x] [Branch and Bound](/src/Theory/LinearArithmatic/FourierMotzkin.hs)
* Non-Linear Arithmatic
  * [ ] [Interval Constraint Propagation](/src/Theory/NonLinearArithmatic/IntervalConstraintPropagation.hs)
  * [ ] [Subtropical Satisfiability](/src/Theory/NonLinearArithmatic/Subtropical.hs)
  * [ ] [Cylindtrical Algebraic Decomposition](/src/Theory/NonLinearArithmatic/CAD.hs)
  * [ ] Virtual Substitution

