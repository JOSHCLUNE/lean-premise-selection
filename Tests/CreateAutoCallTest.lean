import Duper
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Sqrt
import KNNPremiseSelection.Tactic
import KNNPremiseSelection.Widget

set_option trace.suggestPremises.debug true

set_option auto.tptp true
set_option auto.tptp.premiseSelection true
set_option auto.tptp.solver.name "zipperposition"
set_option trace.auto.tptp.result true
set_option trace.auto.tptp.printQuery true
set_option auto.native true

open Lean Auto

@[rebind Auto.Native.solverFunc]
def Auto.duperPort (lemmas : Array Lemma) : MetaM Expr := do
  /- Adding `isFromGoal := false` to each formula because there is no means of distinguishing goal formulas
     from non-goal formulas in this context -/
  let formulas : Array (Expr × Expr × Array Name × Bool) ←
    lemmas.mapM (fun lem => do return (lem.type, ← Meta.mkAppM ``eq_true #[lem.proof], #[], false))
  runDuperPortfolioMode formulas.data .none
    { portfolioMode := true,
      portfolioInstance := none,
      inhabitationReasoning := none,
      preprocessing := PreprocessingOption.NoPreprocessing, -- It would be redundant to enable Auto's preprocessing for Auto calls
      includeExpensiveRules := none,
      selFunction := none
    }
    .none

example {G : Type} [hG : Group G] (x y : G) : x * y * y⁻¹ = x := by
  -- duper [mul_left_inv, one_mul, mul_assoc] {portfolioInstance := 1}
  -- create_auto_call works
  -- create_auto_call_knn works
  sorry

/- Note for the two examples that fail: `abs_add` does not appear in either the forest file or
   the label files. Both `sub_le_iff_le_add` and `sub_add_cancel` appear in both -/

-- This example is the same as the next example except it is maximally general
example {G : Type} [LinearOrderedAddCommGroup G] (a b : G) : |a| - |b| ≤ |a - b| := by
  -- duper [sub_le_iff_le_add, sub_add_cancel, abs_add] {portfolioInstance := 1}
  /- create_auto_call_knn doesn't work (is missing abs_add, and fails even if abs_add is added
      because of the number of other irrelevant premises suggested) -/
  /- create_auto_call doesn't work (is missing sub_add_cancel and abs_add, and fails even if
      they are added because of the number of other irrelevant premises suggested) -/
  /- Note: abs_add appears to genuinely be missing from the knn filter. I couldn't find its
     score at all even after modifying `show_premise_list_knn` to specifically show it -/
  sorry

-- This example is the same as the previous example except it is specialized to Reals. The relevance
-- filter behaves differently from the previous example (it no longer supplies sub_le_iff_le_add)
example (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  -- duper [sub_le_iff_le_add, sub_add_cancel, abs_add] {portfolioInstance := 1}
  /- create_auto_call_knn doesn't work (is missing abs_add, and fails even if abs_add is added
      because of the number of other irrelevant premises suggested) -/
  /- create_auto_call doesn't work (auto can't process at least one of the suggested lemmas) -/
  sorry

example {s t : Set α} (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  -- duper [Set.mem_inter_iff, Set.subset_def, h]
  -- create_auto_call_knn works (I just need to remember to add `*` so `h` can be used)
  -- create_auto_call also works (again, as long as I add `*` so `h` can be used)
  sorry
