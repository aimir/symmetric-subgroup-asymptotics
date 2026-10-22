import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoProjectiveEquiv
import SymmetricSubgroupAsymptotics.CFSGSymplecticSimpleIndexReduction

/-! Both quantitative simple-index conclusions for the original
characteristic-two B family, via the proved actual projective C quotient.
C simplicity is transferred from the original B model, not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley CFSGReduction PrimitiveSocleRawStructure
variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem serre_charTwo_simpleIndexBounds (r : ℕ) (hr : 2 ≤ r)
    [IsSimpleGroup (Projective (CartanMatrix.B (r + 1)).transpose K)] :
    ∀ ell : ℕ, LeastProperIndex (Projective (CartanMatrix.B (r + 1)).transpose K) ell →
      ell ^ 2 < Nat.card (Projective (CartanMatrix.B (r + 1)).transpose K) ∧
        (Nat.card (Outer (Projective (CartanMatrix.B (r + 1)).transpose K)) : ℝ) ≤
          3 * Real.logb 2 ell := by
  let e := serreProjectiveEquivSymplecticProjective_charTwo K r (by omega)
  letI charTwoB_symplecticProjectiveSimple :
      IsSimpleGroup (CFSGSymplecticSerreMatrices.elementaryProjective K (r + 1)) :=
    e.symm.isSimpleGroup
  apply simpleIndexBounds_of_mulEquiv e
  intro ell hell
  refine ⟨CFSGSymplecticSerreMatrices.elementary_leastProperIndex_square_lt_card K r
    (by omega) (by omega) ell hell, ?_⟩
  obtain ⟨H, hH, hi⟩ := hell.1
  have hqell : Nat.card K ≤ ell := by
    have h := CFSGSymplecticSerreMatrices.projective_field_card_le_proper_index K r
      (by omega) H hH
    rwa [hi] at h
  have hf := CFSGFiniteFieldAutomorphisms.card_ringAut_le_logb K
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (Nat.card_pos (α := K)) : (0 : ℝ) < Nat.card K)
    (by exact_mod_cast hqell : (Nat.card K : ℝ) ≤ ell)
  have hout : (Nat.card (Outer (CFSGSymplecticSerreMatrices.elementaryProjective K (r + 1))) : ℝ) ≤
      3 * (Nat.card (K ≃+* K) : ℝ) := by
    exact_mod_cast CFSGSymplecticPointRootLabels.binary_outer_card_le (K := K) r (by omega)
  exact hout.trans ((mul_le_mul_of_nonneg_left hf (by norm_num)).trans
    (mul_le_mul_of_nonneg_left hlog (by norm_num)))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeB_charTwo_simpleIndexBounds (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hq : q.prime = 2) [IsSimpleGroup (CFSG.Models.B r q)] :
    ModelSimpleIndexBounds (.B r q hr) := by
  letI charTwoB_simpleIndexField : CharP q.Field 2 := by rw [← hq]; infer_instance
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 1 := ⟨r - 1, by omega⟩
  exact CFSGOrthogonalBSerreMatrices.serre_charTwo_simpleIndexBounds q.Field s (by omega)

end SymmetricSubgroupAsymptotics.CFSGReduction
