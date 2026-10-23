import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHalfDecomposition
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMixedTracePencil

/-! Actual linear projection onto the four-dimensional coordinate
half-sum, with its literal anisotropic middle vector and perpendicular.
These coordinates will discharge the outside-neighbor obstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

def unitaryRankFourMiddle (q : CFSG.PrimePower) : Fin 5 → q.Extension 2 := Pi.single 2 1

def unitaryRankFourHalf (q : CFSG.PrimePower) : Submodule (q.Extension 2) (Fin 5 → q.Extension 2) :=
  unitaryStandardSingularSpace q 4 ⊔ unitaryOppositeSingularSpace q 4

def unitaryRankFourProjection (q : CFSG.PrimePower) :
    (Fin 5 → q.Extension 2) →ₗ[q.Extension 2] (Fin 5 → q.Extension 2) :=
  LinearMap.id - (LinearMap.proj (2 : Fin 5)).smulRight (unitaryRankFourMiddle q)

theorem unitaryRankFourProjection_apply (q : CFSG.PrimePower) (x : Fin 5 → q.Extension 2) :
    unitaryRankFourProjection q x = x - x 2 • unitaryRankFourMiddle q := rfl

theorem unitaryRankFourHalf_middle_zero (q : CFSG.PrimePower)
    (x : Fin 5 → q.Extension 2) (hx : x ∈ unitaryRankFourHalf q) : x 2 = 0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  have hu0 : u 2 = 0 := hu 2 (by decide)
  have hv0 := (unitaryOppositeSingularSpace_mem_iff q 4 v).mp hv (2 : Fin 5)
  have hrev : (2 : Fin 5).rev = 2 := by decide
  rw [hrev] at hv0
  change u 2 + v 2 = 0
  rw [hu0, hv0 (by decide), zero_add]

theorem unitaryRankFourCentralProjection (q : CFSG.PrimePower) (x : Fin 5 → q.Extension 2) :
    unitaryCentralCoordinateProjection q 4 x = x 2 • unitaryRankFourMiddle q := by
  ext i
  fin_cases i <;> norm_num [unitaryCentralCoordinateProjection, unitaryRankFourMiddle,
    Pi.single_apply, Fin.ext_iff]
  rfl

theorem unitaryRankFourProjection_mem (q : CFSG.PrimePower) (x : Fin 5 → q.Extension 2) :
    unitaryRankFourProjection q x ∈ unitaryRankFourHalf q := by
  have hh := unitary_half_decomposition q 4 x
  rw [unitaryRankFourCentralProjection] at hh
  have he : unitaryRankFourProjection q x = unitaryStandardProjection q 4 x + unitaryOppositeProjection q 4 x := by
    rw [unitaryRankFourProjection_apply]
    exact sub_eq_iff_eq_add.mpr hh
  rw [he]
  exact Submodule.add_mem_sup (unitaryStandardProjection_mem q 4 x) (unitaryOppositeProjection_mem q 4 x)

theorem unitaryRankFourProjection_middle (q : CFSG.PrimePower) :
    unitaryRankFourProjection q (unitaryRankFourMiddle q) = 0 := by
  rw [unitaryRankFourProjection_apply]
  simp only [unitaryRankFourMiddle, Pi.single_eq_same, one_smul, sub_self]

theorem unitaryRankFourProjection_decomposition (q : CFSG.PrimePower) (x : Fin 5 → q.Extension 2) :
    x = unitaryRankFourProjection q x + x 2 • unitaryRankFourMiddle q := by
  rw [unitaryRankFourProjection_apply, sub_add_cancel]

theorem unitaryRankFourMiddle_ne_zero (q : CFSG.PrimePower) : unitaryRankFourMiddle q ≠ 0 := by
  intro h
  have hh := congrFun h (2 : Fin 5)
  change (1 : q.Extension 2) = 0 at hh
  exact (one_ne_zero : (1 : q.Extension 2) ≠ 0) hh

theorem unitaryRankFourMiddle_norm (q : CFSG.PrimePower) :
    unitaryNaturalPair q 4 (unitaryRankFourMiddle q) (unitaryRankFourMiddle q) = 1 := by
  change unitaryNaturalPair q 4 (Pi.single (2 : Fin 5) 1) (Pi.single 2 1) = 1
  rw [unitaryNaturalPair_basis]
  norm_num [signWeight, Fin.rev, Pi.single_apply, Fin.ext_iff]

theorem unitaryRankFourMiddle_perp_half (q : CFSG.PrimePower) :
    unitaryRankFourMiddle q ∈ rightPerp (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) (unitaryRankFourHalf q) := by
  intro x hx
  have hx0 := unitaryRankFourHalf_middle_zero q x hx
  change unitaryNaturalPair q 4 x (Pi.single (2 : Fin 5) 1) = 0
  rw [unitaryRankFour_pair_reciprocal, unitaryNaturalPair_basis]
  have he : (2 : Fin 5).rev = 2 := by decide
  rw [he, hx0, mul_zero, map_zero]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
