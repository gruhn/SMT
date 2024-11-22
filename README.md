Not really usable as a fully fledged SMT solver right now.
Mainly just a collection of various algorithms used in SMT solvers, implemented in Haskell:

* SAT solving
  * [Davis–Putnam–Logemann–Loveland (DPLL)](/src/SAT/DPLL.hs)
  * [Conflict Driven Clause Learning (CDCL)](/src/SAT/CDCL.hs)
* Uninterpreted Functions
  * [Congruence Closure](/src/Theory/UninterpretedFunctions.hs)
* Linear Arithmatic
  * [Simplex Method](/src/Theory/LinearArithmatic/Simplex.hs)
  * [Fourier-Motzkin](/src/Theory/LinearArithmatic/FourierMotzkin.hs)
  * [Branch and Bound](/src/Theory/LinearArithmatic/BranchAndBound.hs)
* Non-Linear Arithmatic
  * [Interval Constraint Propagation](/src/Theory/NonLinearRealArithmatic/IntervalConstraintPropagation.hs)
  * [Subtropical Satisfiability](/src/Theory/NonLinearRealArithmatic/Subtropical.hs)
  * [Cylindtrical Algebraic Decomposition](/src/Theory/NonLinearRealArithmatic/CAD.hs)
  * Virtual Substitution

