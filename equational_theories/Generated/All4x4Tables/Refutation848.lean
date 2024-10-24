
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,0,3],[4,1,3,2,0],[2,3,1,4,2],[3,4,2,3,1],[0,2,4,1,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,0,3],[4,1,3,2,0],[2,3,1,4,2],[3,4,2,3,1],[0,2,4,1,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,0,0,3],[4,1,3,2,0],[2,3,1,4,2],[3,4,2,3,1],[0,2,4,1,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,0,3],[4,1,3,2,0],[2,3,1,4,2],[3,4,2,3,1],[0,2,4,1,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [633] [411, 4380] :=
    ⟨Fin 5, «FinitePoly [[1,2,0,0,3],[4,1,3,2,0],[2,3,1,4,2],[3,4,2,3,1],[0,2,4,1,4]]», Finite.of_fintype _, by decideFin!⟩