import SymmetricSubgroupAsymptotics.CFSGTwistedDFrameReduction
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneUnits
import Mathlib.Tactic.LinearCombination

/-! The actual final plane left by frame reduction is diagonal or
antidiagonal, with a literal norm-one extension-field unit as parameter.
The two components are retained separately, also in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDResidualPlane
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexTailCoordinates CFSGTwistedDNaturalFieldTwist
open CFSGTwistedDNormOneUnits CFSGSerreOrdinaryTwists

theorem diagonal_or_antidiagonal (K : Type) [Field K] (A : Mat K 1)
    (hQ : ∀ v : Index 1 → K, splitQ K (A *ᵥ v) = splitQ K v) :
    ∃ c : Kˣ,
      (A (Sum.inl 0) (Sum.inl 0) = c ∧ A (Sum.inl 0) (Sum.inr 0) = 0 ∧
        A (Sum.inr 0) (Sum.inl 0) = 0 ∧ A (Sum.inr 0) (Sum.inr 0) = (c : K)⁻¹) ∨
      (A (Sum.inl 0) (Sum.inl 0) = 0 ∧ A (Sum.inl 0) (Sum.inr 0) = c ∧
        A (Sum.inr 0) (Sum.inl 0) = (c : K)⁻¹ ∧ A (Sum.inr 0) (Sum.inr 0) = 0) := by
  have h00 : A (Sum.inl 0) (Sum.inl 0) * A (Sum.inr 0) (Sum.inl 0) = 0 := by
    simpa [splitQ, leftPart, rightPart, dotProduct, Matrix.mulVec_single_one, Matrix.col]
      using hQ (Pi.single (Sum.inl 0) 1)
  have h11 : A (Sum.inl 0) (Sum.inr 0) * A (Sum.inr 0) (Sum.inr 0) = 0 := by
    simpa [splitQ, leftPart, rightPart, dotProduct, Matrix.mulVec_single_one, Matrix.col]
      using hQ (Pi.single (Sum.inr 0) 1)
  have hs : (A (Sum.inl 0) (Sum.inl 0) + A (Sum.inl 0) (Sum.inr 0)) *
      (A (Sum.inr 0) (Sum.inl 0) + A (Sum.inr 0) (Sum.inr 0)) = 1 := by
    have h := hQ (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)
    rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa [splitQ, leftPart, rightPart, dotProduct, Pi.add_apply, Matrix.col] using h
  have hc : A (Sum.inl 0) (Sum.inl 0) * A (Sum.inr 0) (Sum.inr 0) +
      A (Sum.inl 0) (Sum.inr 0) * A (Sum.inr 0) (Sum.inl 0) = 1 := by
    linear_combination hs - h00 - h11
  by_cases ha : A (Sum.inl 0) (Sum.inl 0) = 0
  · have hp : A (Sum.inl 0) (Sum.inr 0) * A (Sum.inr 0) (Sum.inl 0) = 1 := by
      simpa only [ha, zero_mul, zero_add] using hc
    have hb : A (Sum.inl 0) (Sum.inr 0) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hp
      exact zero_ne_one hp
    have hd : A (Sum.inr 0) (Sum.inr 0) = 0 := (mul_eq_zero.mp h11).resolve_left hb
    have hi : A (Sum.inr 0) (Sum.inl 0) = (A (Sum.inl 0) (Sum.inr 0))⁻¹ := by
      apply mul_left_cancel₀ hb
      rw [hp, mul_inv_cancel₀ hb]
    exact ⟨Units.mk0 (A (Sum.inl 0) (Sum.inr 0)) hb, Or.inr ⟨ha, rfl, hi, hd⟩⟩
  · have hz : A (Sum.inr 0) (Sum.inl 0) = 0 := (mul_eq_zero.mp h00).resolve_left ha
    have hp : A (Sum.inl 0) (Sum.inl 0) * A (Sum.inr 0) (Sum.inr 0) = 1 := by
      simpa only [hz, mul_zero, add_zero] using hc
    have hd : A (Sum.inr 0) (Sum.inr 0) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hp
      exact zero_ne_one hp
    have hb : A (Sum.inl 0) (Sum.inr 0) = 0 := (mul_eq_zero.mp h11).resolve_right hd
    have hi : A (Sum.inr 0) (Sum.inr 0) = (A (Sum.inl 0) (Sum.inl 0))⁻¹ := by
      apply mul_left_cancel₀ ha
      rw [hp, mul_inv_cancel₀ ha]
    exact ⟨Units.mk0 (A (Sum.inl 0) (Sum.inl 0)) ha, Or.inl ⟨rfl, hb, hz, hi⟩⟩

theorem fixed_entries (q : CFSG.PrimePower) (b : (Mat (q.Extension 2) 1)ˣ)
    (ht : unitTwist (q.Extension 2) 0 (definingFieldAutomorphism q 2)
      (tailUnitHom (q.Extension 2) 1 b) = tailUnitHom (q.Extension 2) 1 b) :
    definingFieldAutomorphism q 2 ((b : Mat (q.Extension 2) 1) (Sum.inl 0) (Sum.inl 0)) =
        (b : Mat (q.Extension 2) 1) (Sum.inr 0) (Sum.inr 0) ∧
      definingFieldAutomorphism q 2 ((b : Mat (q.Extension 2) 1) (Sum.inl 0) (Sum.inr 0)) =
        (b : Mat (q.Extension 2) 1) (Sum.inr 0) (Sum.inl 0) := by
  have hs : (CFSGOrthogonalDGenerationForkTorus.flip 0).symm (Sum.inr (1 : Fin 2)) =
      Sum.inl (1 : Fin 2) := by decide
  have hp : (CFSGOrthogonalDGenerationForkTorus.flip 0).symm (Sum.inl (1 : Fin 2)) =
      Sum.inr (1 : Fin 2) := by decide
  have hd := congrArg (fun u : (Mat (q.Extension 2) 2)ˣ =>
    (u : Mat (q.Extension 2) 2) (Sum.inr 1) (Sum.inr 1)) ht
  have ho := congrArg (fun u : (Mat (q.Extension 2) 2)ˣ =>
    (u : Mat (q.Extension 2) 2) (Sum.inr 1) (Sum.inl 1)) ht
  change definingFieldAutomorphism q 2
    (tailMatrixHom (q.Extension 2) 1 (b : Mat (q.Extension 2) 1)
      ((CFSGOrthogonalDGenerationForkTorus.flip 0).symm (Sum.inr 1))
      ((CFSGOrthogonalDGenerationForkTorus.flip 0).symm (Sum.inr 1))) =
        tailMatrixHom (q.Extension 2) 1 (b : Mat (q.Extension 2) 1) (Sum.inr 1) (Sum.inr 1) at hd
  change definingFieldAutomorphism q 2
    (tailMatrixHom (q.Extension 2) 1 (b : Mat (q.Extension 2) 1)
      ((CFSGOrthogonalDGenerationForkTorus.flip 0).symm (Sum.inr 1))
      ((CFSGOrthogonalDGenerationForkTorus.flip 0).symm (Sum.inl 1))) =
        tailMatrixHom (q.Extension 2) 1 (b : Mat (q.Extension 2) 1) (Sum.inr 1) (Sum.inl 1) at ho
  rw [hs] at hd
  rw [hs, hp] at ho
  change definingFieldAutomorphism q 2
    (tailMatrixHom (q.Extension 2) 1 (b : Mat (q.Extension 2) 1)
      (tailIndex 1 (Sum.inl 0)) (tailIndex 1 (Sum.inl 0))) =
        tailMatrixHom (q.Extension 2) 1 (b : Mat (q.Extension 2) 1)
          (tailIndex 1 (Sum.inr 0)) (tailIndex 1 (Sum.inr 0)) at hd
  change definingFieldAutomorphism q 2
    (tailMatrixHom (q.Extension 2) 1 (b : Mat (q.Extension 2) 1)
      (tailIndex 1 (Sum.inl 0)) (tailIndex 1 (Sum.inr 0))) =
        tailMatrixHom (q.Extension 2) 1 (b : Mat (q.Extension 2) 1)
          (tailIndex 1 (Sum.inr 0)) (tailIndex 1 (Sum.inl 0)) at ho
  simpa only [tailMatrixHom_tail_tail] using And.intro hd ho

theorem normOne_of_frobenius_inv (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (hc : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2)⁻¹) :
    c ∈ normOneUnits q := by
  change c ^ (q.order + 1) = 1
  apply Units.ext
  change (c : q.Extension 2) ^ (q.order + 1) = 1
  rw [pow_succ, ← definingFieldAutomorphism_apply, hc, inv_mul_cancel₀ (Units.ne_zero c)]

theorem exists_normOne_form (q : CFSG.PrimePower) (b : quadraticPreserving (q.Extension 2) 1)
    (ht : unitTwist (q.Extension 2) 0 (definingFieldAutomorphism q 2)
      (tailUnitHom (q.Extension 2) 1 b.val) = tailUnitHom (q.Extension 2) 1 b.val) :
    ∃ c : normOneUnits q,
      ((b.val : Mat (q.Extension 2) 1) (Sum.inl 0) (Sum.inl 0) = c.val ∧
        (b.val : Mat (q.Extension 2) 1) (Sum.inl 0) (Sum.inr 0) = 0 ∧
        (b.val : Mat (q.Extension 2) 1) (Sum.inr 0) (Sum.inl 0) = 0 ∧
        (b.val : Mat (q.Extension 2) 1) (Sum.inr 0) (Sum.inr 0) = (c.val : q.Extension 2)⁻¹) ∨
      ((b.val : Mat (q.Extension 2) 1) (Sum.inl 0) (Sum.inl 0) = 0 ∧
        (b.val : Mat (q.Extension 2) 1) (Sum.inl 0) (Sum.inr 0) = c.val ∧
        (b.val : Mat (q.Extension 2) 1) (Sum.inr 0) (Sum.inl 0) = (c.val : q.Extension 2)⁻¹ ∧
        (b.val : Mat (q.Extension 2) 1) (Sum.inr 0) (Sum.inr 0) = 0) := by
  obtain ⟨c, hc⟩ := diagonal_or_antidiagonal (q.Extension 2) (b.val : Mat (q.Extension 2) 1) b.property
  have he := fixed_entries q b.val ht
  rcases hc with hc | hc
  · have hσ : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2)⁻¹ := by
      rw [hc.1, hc.2.2.2] at he
      exact he.1
    exact ⟨⟨c, normOne_of_frobenius_inv q c hσ⟩, Or.inl hc⟩
  · have hσ : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2)⁻¹ := by
      rw [hc.2.1, hc.2.2.1] at he
      exact he.2
    exact ⟨⟨c, normOne_of_frobenius_inv q c hσ⟩, Or.inr hc⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDResidualPlane
