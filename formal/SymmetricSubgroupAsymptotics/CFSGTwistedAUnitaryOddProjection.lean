import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHalfDecomposition
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMixedPencil

/-! Literal opposed projection in every odd vector dimension at least five.
The central signed norm is retained; its sign is not assumed positive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

def unitaryOddMiddleIndex (m : ℕ) : Fin (2*m+5) := ⟨m+2, by omega⟩

theorem unitaryOddMiddleIndex_rev (m : ℕ) :
    (unitaryOddMiddleIndex m).rev = unitaryOddMiddleIndex m := by
  apply Fin.ext
  simp only [Fin.val_rev, unitaryOddMiddleIndex]
  omega

def unitaryOddMiddle (q : CFSG.PrimePower) (m : ℕ) : Fin (2*m+5) → q.Extension 2 :=
  Pi.single (unitaryOddMiddleIndex m) 1

def unitaryOddHalf (q : CFSG.PrimePower) (m : ℕ) :
    Submodule (q.Extension 2) (Fin (2*m+5) → q.Extension 2) :=
  unitaryStandardSingularSpace q (2*m+4) ⊔ unitaryOppositeSingularSpace q (2*m+4)

def unitaryOddProjection (q : CFSG.PrimePower) (m : ℕ) :
    (Fin (2*m+5) → q.Extension 2) →ₗ[q.Extension 2] (Fin (2*m+5) → q.Extension 2) :=
  LinearMap.id - (LinearMap.proj (unitaryOddMiddleIndex m)).smulRight (unitaryOddMiddle q m)

theorem unitaryOddProjection_apply (q : CFSG.PrimePower) (m : ℕ)
    (x : Fin (2*m+5) → q.Extension 2) :
    unitaryOddProjection q m x = x - x (unitaryOddMiddleIndex m) • unitaryOddMiddle q m := rfl

theorem unitaryOddHalf_middle_zero (q : CFSG.PrimePower) (m : ℕ)
    (x : Fin (2*m+5) → q.Extension 2) (hx : x ∈ unitaryOddHalf q m) :
    x (unitaryOddMiddleIndex m) = 0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  have hu0 : u (unitaryOddMiddleIndex m) = 0 := hu _ (by
    change 2*m+4 < 2*(m+2)+1
    omega)
  have hv0 := (unitaryOppositeSingularSpace_mem_iff q (2*m+4) v).mp hv (unitaryOddMiddleIndex m)
  rw [unitaryOddMiddleIndex_rev] at hv0
  have hv1 : v (unitaryOddMiddleIndex m) = 0 := hv0 (by
    change 2*m+4 < 2*(m+2)+1
    omega)
  change u (unitaryOddMiddleIndex m) + v (unitaryOddMiddleIndex m) = 0
  rw [hu0, hv1, zero_add]

theorem unitaryOddCentralProjection (q : CFSG.PrimePower) (m : ℕ)
    (x : Fin (2*m+5) → q.Extension 2) :
    unitaryCentralCoordinateProjection q (2*m+4) x =
      x (unitaryOddMiddleIndex m) • unitaryOddMiddle q m := by
  funext i
  by_cases hi : i = unitaryOddMiddleIndex m
  · subst i
    have hm : 2*(m+2) = 2*m+4 := by omega
    simp [unitaryCentralCoordinateProjection, unitaryOddMiddle, unitaryOddMiddleIndex, hm]
  · have hne : ¬2*i.val = 2*m+4 := by
      intro h
      apply hi
      apply Fin.ext
      change i.val = m+2
      omega
    simp [unitaryCentralCoordinateProjection, hne, unitaryOddMiddle, hi]

theorem unitaryOddProjection_mem (q : CFSG.PrimePower) (m : ℕ)
    (x : Fin (2*m+5) → q.Extension 2) : unitaryOddProjection q m x ∈ unitaryOddHalf q m := by
  have hh := unitary_half_decomposition q (2*m+4) x
  rw [unitaryOddCentralProjection] at hh
  have he : unitaryOddProjection q m x = unitaryStandardProjection q (2*m+4) x +
      unitaryOppositeProjection q (2*m+4) x := by
    rw [unitaryOddProjection_apply]
    exact sub_eq_iff_eq_add.mpr hh
  rw [he]
  exact Submodule.add_mem_sup (unitaryStandardProjection_mem q (2*m+4) x)
    (unitaryOppositeProjection_mem q (2*m+4) x)

theorem unitaryOddProjection_middle (q : CFSG.PrimePower) (m : ℕ) :
    unitaryOddProjection q m (unitaryOddMiddle q m) = 0 := by
  rw [unitaryOddProjection_apply]
  simp only [unitaryOddMiddle, Pi.single_eq_same, one_smul, sub_self]

theorem unitaryOddProjection_decomposition (q : CFSG.PrimePower) (m : ℕ)
    (x : Fin (2*m+5) → q.Extension 2) :
    x = unitaryOddProjection q m x + x (unitaryOddMiddleIndex m) • unitaryOddMiddle q m := by
  rw [unitaryOddProjection_apply, sub_add_cancel]

theorem unitaryOddMiddle_ne_zero (q : CFSG.PrimePower) (m : ℕ) : unitaryOddMiddle q m ≠ 0 := by
  intro h
  have hh := congrFun h (unitaryOddMiddleIndex m)
  simp only [unitaryOddMiddle, Pi.single_eq_same, Pi.zero_apply] at hh
  exact one_ne_zero hh

theorem unitaryOddMiddle_norm (q : CFSG.PrimePower) (m : ℕ) :
    unitaryNaturalPair q (2*m+4) (unitaryOddMiddle q m) (unitaryOddMiddle q m) =
      signWeight (q.Extension 2) (2*m+4) (unitaryOddMiddleIndex m) := by
  change unitaryNaturalPair q (2*m+4) (Pi.single (unitaryOddMiddleIndex m) 1)
    (Pi.single (unitaryOddMiddleIndex m) 1) = _
  rw [unitaryNaturalPair_basis, unitaryOddMiddleIndex_rev, Pi.single_eq_same, mul_one]

theorem unitaryOddMiddle_norm_ne_zero (q : CFSG.PrimePower) (m : ℕ) :
    unitaryNaturalPair q (2*m+4) (unitaryOddMiddle q m) (unitaryOddMiddle q m) ≠ 0 := by
  rw [unitaryOddMiddle_norm]
  exact signWeight_ne_zero _ _ _

theorem unitaryOddMiddle_perp_half (q : CFSG.PrimePower) (m : ℕ) :
    unitaryOddMiddle q m ∈ rightPerp (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4))
      (unitaryOddHalf q m) := by
  intro x hx
  have hx0 := unitaryOddHalf_middle_zero q m x hx
  change unitaryNaturalPair q (2*m+4) x (Pi.single (unitaryOddMiddleIndex m) 1) = 0
  rw [unitary_oddSpace_pair_reciprocal q (2*m+4) (by exact ⟨m+2, by omega⟩),
    unitaryNaturalPair_basis, unitaryOddMiddleIndex_rev, hx0, mul_zero, map_zero]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
