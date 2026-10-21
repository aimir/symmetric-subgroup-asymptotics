import SymmetricSubgroupAsymptotics.CFSGSuzukiCentralPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds

/-! Numerical consequences of the actual central-root permutation bound.
The extension exponent is at most log₂ of the actual least proper index.
The final assembler still takes the separate outer-cardinality theorem;
it does not assert that automorphism reconstruction is already complete. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiIndexNumerics
open CFSGSuzukiFieldParameters CFSGSuzukiCentralPermutationDegree
open CFSGSuzukiLeastIndexOrder PrimitiveSocleRawStructure

theorem extensionDegree_le_logb_leastProperIndex (m ell : ℕ)
    [IsSimpleGroup (CFSG.Models.Suzuki m)]
    (hell : LeastProperIndex (CFSG.Models.Suzuki m) ell) :
    (2*m+1 : ℕ) ≤ Real.logb 2 ell := by
  have hn := field_card_le_leastProperIndex m ell hell
  rw [field_card] at hn
  have hr : (2 : ℝ)^(2*m+1)≤(ell : ℝ) := by exact_mod_cast hn
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by positivity : (0 : ℝ)<(2 : ℝ)^(2*m+1)) hr
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] using hl

theorem simpleIndexBounds_of_outer_card (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.Suzuki m)]
    (hOut : Nat.card (Outer (CFSG.Models.Suzuki m))≤2*m+1)
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.Suzuki m) ell) :
    ell^2<Nat.card (CFSG.Models.Suzuki m) ∧
      (Nat.card (Outer (CFSG.Models.Suzuki m)) : ℝ)≤3*Real.logb 2 ell := by
  refine ⟨leastProperIndex_square_lt_card m hm ell hell,?_⟩
  have hcard : (Nat.card (Outer (CFSG.Models.Suzuki m)) : ℝ)≤(2*m+1 : ℕ) := by
    exact_mod_cast hOut
  have hlog := extensionDegree_le_logb_leastProperIndex m ell hell
  have hnonneg : 0≤Real.logb 2 ell := (Nat.cast_nonneg (2*m+1)).trans hlog
  exact hcard.trans (hlog.trans (by linarith))

end SymmetricSubgroupAsymptotics.CFSGSuzukiIndexNumerics
