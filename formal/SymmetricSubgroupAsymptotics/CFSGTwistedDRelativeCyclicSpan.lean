import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Module

/-! The actual paired terminal words separate both extension-field
axes. This elementary spanning argument uses a genuinely nonfixed
coefficient, and therefore also works over the quadratic extension of F2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCyclicSpan
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDForkPairAction CFSGTwistedDRelativeElementaryGroup
open CFSGSerreOrdinaryTwists

theorem eq_top_of_paired_words (K : Type) [Field K] (n : ℕ) (σ : K ≃+* K)
    (θ : K) (hθ : σ θ ≠ θ) (S : Submodule K (Index (n + 2) → K))
    (hb : ∀ i : Fin (n + 2), i ≠ last n →
      (Pi.single (Sum.inl i) 1 : Index (n + 2) → K) ∈ S ∧
      (Pi.single (Sum.inr i) 1 : Index (n + 2) → K) ∈ S)
    (hp : ∀ a : K, (forkPair K n a (σ a) : Mat K (n + 2)) *ᵥ
      Pi.single (Sum.inr (pen n)) 1 ∈ S) : S = ⊤ := by
  let e : Index (n + 2) → K := Pi.single (Sum.inl (last n)) 1
  let f : Index (n + 2) → K := Pi.single (Sum.inr (last n)) 1
  have htail (a : K) : σ a • e + a • f ∈ S := by
    have hw := hp a
    have heq : (forkPair K n a (σ a) : Mat K (n + 2)) *ᵥ
        Pi.single (Sum.inr (pen n)) 1 =
      Pi.single (Sum.inr (pen n)) 1 - a • f - σ a • e -
        (a * σ a) • Pi.single (Sum.inl (pen n)) 1 := by
      rw [forkPair_mulVec]
      ext x
      cases x with
      | inl i =>
        by_cases hip : i = pen n <;> by_cases hil : i = last n <;>
          simp_all [e, f, Pi.single_apply, smul_eq_mul, pen_ne_last n,
            Ne.symm (pen_ne_last n)]
      | inr i =>
        by_cases hip : i = pen n <;> by_cases hil : i = last n <;>
          simp_all [e, f, Pi.single_apply, smul_eq_mul, pen_ne_last n,
            Ne.symm (pen_ne_last n)]
    rw [heq] at hw
    have hm := S.sub_mem (S.sub_mem (hb (pen n) (pen_ne_last n)).2 hw)
      (S.smul_mem (a * σ a) (hb (pen n) (pen_ne_last n)).1)
    convert hm using 1 <;> module
  have hsum : e + f ∈ S := by simpa only [map_one, one_smul] using htail 1
  have hdiff : (σ θ - θ) • e ∈ S := by
    have hm := S.sub_mem (htail θ) (S.smul_mem θ hsum)
    convert hm using 1 <;> module
  have he : e ∈ S := by
    have hm := S.smul_mem (σ θ - θ)⁻¹ hdiff
    simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hθ), one_smul] using hm
  have hf : f ∈ S := by
    have hm := S.sub_mem hsum he
    convert hm using 1 <;> module
  apply top_unique
  rw [← (Pi.basisFun K (Index (n + 2))).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  simp only [Pi.basisFun_apply]
  cases x with
  | inl i =>
    by_cases hi : i = last n
    · simpa only [hi] using he
    · exact (hb i hi).1
  | inr i =>
    by_cases hi : i = last n
    · simpa only [hi] using hf
    · exact (hb i hi).2

theorem eq_top_of_relative_words (n : ℕ) (q : CFSG.PrimePower)
    (S : Submodule (q.Extension 2) (Index (n + 2) → q.Extension 2))
    (hb : ∀ i : Fin (n + 2), i ≠ last n →
      (Pi.single (Sum.inl i) 1 : Index (n + 2) → q.Extension 2) ∈ S ∧
      (Pi.single (Sum.inr i) 1 : Index (n + 2) → q.Extension 2) ∈ S)
    (hp : ∀ a : q.Extension 2, (pairedRoot n q false a : Mat (q.Extension 2) (n + 2)) *ᵥ
      Pi.single (Sum.inr (pen n)) 1 ∈ S) : S = ⊤ := by
  obtain ⟨θ, hθ⟩ := CFSGTwistedAQuadraticTrace.exists_nonfixed q
  exact eq_top_of_paired_words (q.Extension 2) n (definingFieldAutomorphism q 2) θ hθ S hb hp

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCyclicSpan
