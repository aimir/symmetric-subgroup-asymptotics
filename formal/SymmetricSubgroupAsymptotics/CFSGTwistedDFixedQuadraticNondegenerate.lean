import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCyclicSpan
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizeFirstPair

/-! The actual defining-fixed space spans the original extension-field
space, and its fixed-field quadratic form has nondegenerate polar form.
The paired words provide the missing two axes without division by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticNondegenerate
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeFixedGroup CFSGTwistedDNormalizeFirstPair
open CFSGOrthogonalDIndexBundledQuadratic CFSGSerreOrdinaryTwists

theorem fixedSpace_span (n : ℕ) (q : CFSG.PrimePower) :
    Submodule.span (q.Extension 2) (Set.range (fun v : fixedSpace n q => v.val)) = ⊤ := by
  let S := Submodule.span (q.Extension 2) (Set.range (fun v : fixedSpace n q => v.val))
  have hb (i : Fin (n + 2)) (hi : i ≠ last n) :
      (Pi.single (Sum.inl i) 1 : Index (n + 2) → q.Extension 2) ∈ S ∧
      (Pi.single (Sum.inr i) 1 : Index (n + 2) → q.Extension 2) ∈ S := by
    constructor
    · apply Submodule.subset_span
      exact ⟨⟨_, fixed_basis _ n _ _
        (by rw [CFSGTwistedDNaturalFork.flip_pos, if_neg hi])⟩, rfl⟩
    · apply Submodule.subset_span
      exact ⟨⟨_, fixed_basis _ n _ _
        (by rw [CFSGTwistedDNaturalFork.flip_neg, if_neg hi])⟩, rfl⟩
  apply CFSGTwistedDRelativeCyclicSpan.eq_top_of_relative_words n q S hb
  intro a
  apply Submodule.subset_span
  have hf := fixed_basis (q.Extension 2) n (definingFieldAutomorphism q 2)
    (Sum.inr (pen n)) (by rw [CFSGTwistedDNaturalFork.flip_neg, if_neg (pen_ne_last n)])
  exact ⟨⟨_, relative_preserves_fixed_vectors n q
    ⟨pairedRoot n q false a, paired_mem n q false a⟩ _ hf⟩, rfl⟩

theorem fixedQuadraticForm_nondegenerate (n : ℕ) (q : CFSG.PrimePower) :
    (fixedQuadraticForm n q).polarBilin.Nondegenerate := by
  have hsep (v : fixedSpace n q)
      (hv : ∀ w : fixedSpace n q, (fixedQuadraticForm n q).polarBilin v w = 0) : v = 0 := by
    let l := (splitQuadraticForm (q.Extension 2) (n + 2)).polarBilin v.val
    have hk : Submodule.span (q.Extension 2) (Set.range (fun w : fixedSpace n q => w.val)) ≤ l.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      have h := congrArg (fun a : CFSGTwistedA2FixedField.fixedField q => (a : q.Extension 2)) (hv w)
      dsimp only at h
      rw [fixedQuadraticForm_polar] at h
      exact h
    rw [fixedSpace_span n q] at hk
    have hz : v.val = 0 := (splitQuadraticForm_nondegenerate (q.Extension 2) (n + 2)).1
      v.val (fun w => hk (show w ∈ (⊤ : Submodule (q.Extension 2) _) from trivial))
    exact Subtype.ext hz
  refine ⟨hsep, fun v hv => hsep v (fun w => ?_)⟩
  have h := hv w
  simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticNondegenerate
