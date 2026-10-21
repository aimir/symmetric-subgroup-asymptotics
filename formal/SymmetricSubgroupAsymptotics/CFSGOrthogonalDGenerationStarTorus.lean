import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialRootMatrices

/-! The literal SL2 torus on the recovered star root. Its membership
uses the two actual star root lines, and its diagonal acts at coordinates
1 and last. This is the torus used after conjugating the whole subgroup
in the second endpoint geometry. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationStarTorus
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationInitialRootMatrices
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDGenerationSignedPermutation
variable (K : Type) [Field K]

def starTorus (s : ℕ) (g : Kˣ) : elementaryRootGroup K (s + 4) :=
  starTransport K s * forkTorus K (s + 2) g * (starTransport K s)⁻¹

theorem starTorus_eq_word (s : ℕ) (g : Kˣ) :
    starTorus K s g =
      initialStarRoot K s false ((g : K) - 1) * initialStarRoot K s true 1 *
        initialStarRoot K s false ((g : K)⁻¹ - 1) * initialStarRoot K s true (-(g : K)) := by
  simp only [starTorus, forkTorus, initialStarRoot]
  group

theorem starTorus_mem (s : ℕ) (g : Kˣ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hpos : ∀ a, (initialStarRoot K s false a).val ∈ H)
    (hneg : ∀ a, (initialStarRoot K s true a).val ∈ H) :
    (starTorus K s g).val ∈ H := by
  rw [starTorus_eq_word]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hpos _) (hneg _)) (hpos _)) (hneg _)

def starDiagonal (s : ℕ) (g : Kˣ) : Index (s + 4) → K
  | Sum.inl i => if i = second s then g else if i = last (s + 2) then g else 1
  | Sum.inr i => if i = second s then (g : K)⁻¹ else if i = last (s + 2) then (g : K)⁻¹ else 1

theorem starTorus_coe (s : ℕ) (g : Kˣ) :
    ((starTorus K s g).val : Mat K (s + 4)) = Matrix.diagonal (starDiagonal K s g) := by
  have hlast : starPermutation s (last (s + 2)) = last (s + 2) := by
    simp [starPermutation, Equiv.swap_apply_def,
      Ne.symm (second_ne_last s), Ne.symm (pen_ne_last (s + 2))]
  have hp (i : Fin (s + 4)) : starPermutation s i = pen (s + 2) ↔ i = second s := by
    constructor
    · intro h
      have hh := congrArg (starPermutation s) h
      simpa [starPermutation] using hh
    · rintro rfl
      simp [starPermutation]
  have hl (i : Fin (s + 4)) : starPermutation s i = last (s + 2) ↔ i = last (s + 2) := by
    constructor
    · intro h
      exact (starPermutation s).injective (h.trans hlast.symm)
    · rintro rfl
      exact hlast
  have hd : forkDiagonal K (s + 2) g ∘ Equiv.sumCongr (starPermutation s) (starPermutation s) =
      starDiagonal K s g := by
    funext x
    cases x <;> simp only [Function.comp_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Sum.map_inr, forkDiagonal, starDiagonal, hp, hl]
  change ((starTransport K s).val : Mat K (s + 4)) *
    ((forkTorus K (s + 2) g).val : Mat K (s + 4)) *
      (↑((starTransport K s).val⁻¹) : Mat K (s + 4)) = _
  rw [forkTorus_coe, ← hd]
  exact CFSGMonomialUnitRootAction.monomial_conjugation_diagonal
    (starTransport K s).val (Equiv.sumCongr (starPermutation s) (starPermutation s))
    (Sum.elim (weight K (0 : Fin (s + 4)) (starPermutation s))
      (weight K (0 : Fin (s + 4)) (starPermutation s)))
    (forkDiagonal K (s + 2) g) (signedPermutationElement_coe K (s + 4) 0 (starPermutation s))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationStarTorus
