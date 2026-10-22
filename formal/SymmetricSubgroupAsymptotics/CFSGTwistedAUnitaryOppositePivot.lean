import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeadOrbit
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryReversalWeyl
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalColumnClearing
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalReversal

/-! A genuine opposite-upper word makes the last coordinate of every
nonzero vector nonzero. It is the literal J*u*J^-1 with u in SAME U;
head separation and the proved signed reversal action supply the pivot.
This is an actual word, not an assumed unitary orbit-transitivity lemma. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

def oppositeNaturalUnipotent (q : CFSG.PrimePower) (r : ℕ) :
    Subgroup (NaturalElementary (q.Extension 2) r) :=
  (naturalUnipotent r q).map (MulAut.conj (reversalNatural q r)).toMonoidHom

theorem signedReversal_mulVec_last (K : Type) [Field K] (r : ℕ) (x : Fin (r + 1) → K) :
    ((signedReversalUnit K r : Mat K r) *ᵥ x) (Fin.last r) =
      signWeight K r (Fin.last r) * x 0 := by
  have hl : (Fin.last r).rev = (0 : Fin (r + 1)) := by
    apply Fin.ext
    simp [Fin.rev]
  simp [Matrix.mulVec, dotProduct, signedReversalUnit_apply, hl, ite_mul]

theorem exists_opposite_last_ne_zero (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2) (hx : x ≠ 0) :
    ∃ v : naturalFixed (s + 2) q,
      v.val ∈ oppositeNaturalUnipotent q (s + 2) ∧
      ((v.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x) (Fin.last (s + 2)) ≠ 0 := by
  let J := signedReversalUnit (q.Extension 2) (s + 2)
  let y : Fin (s + 3) → q.Extension 2 := (↑(J⁻¹) : Mat (q.Extension 2) (s + 2)) *ᵥ x
  have hy : y ≠ 0 := by
    intro hz
    have h := congrArg (fun z => (J : Mat (q.Extension 2) (s + 2)) *ᵥ z) hz
    change (J : Mat (q.Extension 2) (s + 2)) *ᵥ
      ((↑(J⁻¹) : Mat (q.Extension 2) (s + 2)) *ᵥ x) =
      (J : Mat (q.Extension 2) (s + 2)) *ᵥ 0 at h
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h
    exact hx h
  obtain ⟨u, hu⟩ := exists_upper_head_ne_zero q s y hy
  let v : naturalFixed (s + 2) q := reversalFixed q (s + 2) *
    (⟨u.val, u.property.2⟩ : naturalFixed (s + 2) q) * (reversalFixed q (s + 2))⁻¹
  refine ⟨v, ⟨u.val, u.property, rfl⟩, ?_⟩
  have hact : (v.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x =
      (J : Mat (q.Extension 2) (s + 2)) *ᵥ
        ((u.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ y) := by
    change (((J : Mat (q.Extension 2) (s + 2)) *
      (u.val.val : Mat (q.Extension 2) (s + 2))) *
      (↑(J⁻¹) : Mat (q.Extension 2) (s + 2))) *ᵥ x =
      (J : Mat (q.Extension 2) (s + 2)) *ᵥ
        ((u.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ
          ((↑(J⁻¹) : Mat (q.Extension 2) (s + 2)) *ᵥ x))
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  rw [hact]
  change ((signedReversalUnit (q.Extension 2) (s + 2) : Mat (q.Extension 2) (s + 2)) *ᵥ
    ((u.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ y)) (Fin.last (s + 2)) ≠ 0
  rw [signedReversal_mulVec_last]
  exact mul_ne_zero (signWeight_ne_zero (q.Extension 2) (s + 2) _) hu

theorem matrixUnit_column_ne_zero {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (A : (Matrix I I K)ˣ) (j : I) : (fun i => (A : Matrix I I K) i j) ≠ 0 := by
  intro hz
  have he := congrArg (fun M : Matrix I I K => M j j) (Units.inv_mul A)
  have hp : ((↑(A⁻¹) : Matrix I I K) * (A : Matrix I I K)) j j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hi : (A : Matrix I I K) i j = 0 := congrFun hz i
    rw [hi, mul_zero]
  change ((↑(A⁻¹) : Matrix I I K) * (A : Matrix I I K)) j j = (1 : Matrix I I K) j j at he
  rw [Matrix.one_apply_eq] at he
  rw [hp] at he
  exact zero_ne_one he

theorem exists_opposite_first_column_pivot (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q) :
    ∃ v : naturalFixed (s + 2) q,
      v.val ∈ oppositeNaturalUnipotent q (s + 2) ∧
      ((v * g).val.val : Mat (q.Extension 2) (s + 2)) (Fin.last (s + 2)) 0 ≠ 0 := by
  obtain ⟨v, hv, hp⟩ := exists_opposite_last_ne_zero q s
    (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) i 0)
    (matrixUnit_column_ne_zero g.val.val 0)
  exact ⟨v, hv, hp⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
