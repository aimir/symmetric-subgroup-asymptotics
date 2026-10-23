import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedPieceSum
import SymmetricSubgroupAsymptotics.CFSGHermitianRangeIsometry
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedLocalFields
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairReciprocity

/-! Actual partial isometry for the two original unitary coordinate
halves. It is constructed from the literal local point-action pieces,
and its original source range has the proved dimension twice the half
dimension. No target opposed-range normalization is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan CFSGHermitianOpposedSum

abbrev UnitaryOpposedProduct (q : CFSG.PrimePower) (r : ℕ) :=
  (unitaryStandardSingularSpace q r) × (unitaryOppositeSingularSpace q r)

def unitaryOpposedSource (q : CFSG.PrimePower) (r : ℕ) :
    UnitaryOpposedProduct q r →ₗ[q.Extension 2] (Fin (r+1) → q.Extension 2) :=
  sourceSum (unitaryStandardSingularSpace q r) (unitaryOppositeSingularSpace q r)

private theorem opposedPair_add_left (q : CFSG.PrimePower) (r : ℕ)
    (x y z : Fin (r+1) → q.Extension 2) :
    unitaryNaturalPair q r (x+y) z = unitaryNaturalPair q r x z + unitaryNaturalPair q r y z :=
  hermitianPair_add_left (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) x y z

theorem unitaryOpposedSource_nondegenerate (q : CFSG.PrimePower) (r : ℕ)
    (v : UnitaryOpposedProduct q r)
    (hv : ∀ w : UnitaryOpposedProduct q r,
      unitaryNaturalPair q r (unitaryOpposedSource q r v) (unitaryOpposedSource q r w) = 0) : v = 0 := by
  have hx : v.1.val = 0 := by
    apply unitaryStandard_pair_opposite_nondegenerate q r _ v.1.property
    intro z hz
    have hh := hv (0,⟨z,hz⟩)
    change unitaryNaturalPair q r (v.1.val+v.2.val) (0+z) = 0 at hh
    rw [zero_add,opposedPair_add_left,
      unitaryOppositeSingularSpace_pair_zero q r _ _ v.2.property hz,add_zero] at hh
    exact hh
  have hy : v.2.val = 0 := by
    apply unitaryOpposite_pair_standard_nondegenerate q r _ v.2.property
    intro p hp
    have hh := hv (⟨p,hp⟩,0)
    change unitaryNaturalPair q r (v.1.val+v.2.val) (p+0) = 0 at hh
    rw [hx,zero_add,add_zero] at hh
    exact hh
  exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)

theorem unitaryOpposedSource_injective (q : CFSG.PrimePower) (r : ℕ) :
    Function.Injective (unitaryOpposedSource q r) := by
  intro v w he
  apply sub_eq_zero.mp
  apply unitaryOpposedSource_nondegenerate q r
  intro t
  have hh : unitaryOpposedSource q r (v-w) = 0 := by rw [map_sub,he,sub_self]
  rw [hh]
  exact pair_zero_left _ _ _

theorem unitaryOpposedSource_range_nondegenerate (q : CFSG.PrimePower) (r : ℕ) :
    ∀ x ∈ (unitaryOpposedSource q r).range,
      (∀ y ∈ (unitaryOpposedSource q r).range, unitaryNaturalPair q r x y = 0) → x = 0 := by
  rintro x ⟨v,rfl⟩ hv
  have he : v = 0 := unitaryOpposedSource_nondegenerate q r v (fun w => hv _ ⟨w,rfl⟩)
  rw [he,map_zero]

theorem unitaryOpposedSource_range_finrank (q : CFSG.PrimePower) (r : ℕ) :
    Module.finrank (q.Extension 2) (unitaryOpposedSource q r).range = 2 * ((r+1)/2) := by
  rw [LinearMap.finrank_range_of_inj (unitaryOpposedSource_injective q r)]
  change Module.finrank (q.Extension 2)
    ((unitaryStandardSingularSpace q r) × (unitaryOppositeSingularSpace q r)) = _
  rw [Module.finrank_prod,unitaryStandardSingularSpace_finrank,unitaryOppositeSingularSpace_finrank]
  omega

theorem exists_unitary_opposed_partial_isometry (q : CFSG.PrimePower) (r : ℕ) (hr : 3 ≤ r)
    (f : Equiv.Perm (SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f)
    (F : SemilinearPiece (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f
      (unitaryStandardIsotropicSpace q r) (RingEquiv.refl (q.Extension 2)))
    (G : SemilinearPiece (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f
      (unitaryOppositeIsotropicSpace q r) (RingEquiv.refl (q.Extension 2))) :
    ∃ c : q.Extension 2, c ≠ 0 ∧
      ∃ A : (unitaryOpposedSource q r).range →ₗ[q.Extension 2] (Fin (r+1) → q.Extension 2),
        (∀ x y, unitaryNaturalPair q r (A x) (A y) = unitaryNaturalPair q r x.val y.val) ∧
        (∀ p : unitaryStandardSingularSpace q r,
          A (LinearEquiv.ofInjective (unitaryOpposedSource q r) (unitaryOpposedSource_injective q r) (p,0)) = F.map p) ∧
        ∀ z : unitaryOppositeSingularSpace q r,
          A (LinearEquiv.ofInjective (unitaryOpposedSource q r) (unitaryOpposedSource_injective q r) (0,z)) = c⁻¹ • G.map z := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) r := signedReversalUnit (q.Extension 2) r
  let d := (r+1)/2-2
  have hP : Module.finrank (q.Extension 2) (unitaryStandardIsotropicSpace q r).val = d+2 := by
    change Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q r) = d+2
    rw [unitaryStandardSingularSpace_finrank]
    dsimp only [d]
    omega
  have hZ : Module.finrank (q.Extension 2) (unitaryOppositeIsotropicSpace q r).val = d+2 := by
    change Module.finrank (q.Extension 2) (unitaryOppositeSingularSpace q r) = d+2
    rw [unitaryOppositeSingularSpace_finrank]
    dsimp only [d]
    omega
  have hND (x : unitaryStandardSingularSpace q r)
      (hx : ∀ y : unitaryOppositeSingularSpace q r, unitaryNaturalPair q r x.val y.val = 0) : x = 0 := by
    apply Subtype.ext
    exact unitaryStandard_pair_opposite_nondegenerate q r x.val x.property (fun y hy => hx ⟨y,hy⟩)
  obtain ⟨c,hc,hpair⟩ := exists_normalized_opposed_sum sig H f hf
    (unitaryStandardIsotropicSpace q r) (unitaryOppositeIsotropicSpace q r) d hP hZ hND F G
    ((-1 : q.Extension 2)^r) (fun x y => unitaryNaturalPair_signed_reciprocal q r y x)
  let B := imageSum (unitaryStandardSingularSpace q r) (unitaryOppositeSingularSpace q r) F.map (c⁻¹ • G.map)
  let A := CFSGHermitianRangeIsometry.onRange (unitaryOpposedSource q r) (unitaryOpposedSource_injective q r) B
  refine ⟨c,hc,A,CFSGHermitianRangeIsometry.onRange_pair sig H _ _ B hpair,?_,?_⟩
  · intro p
    dsimp only [A]
    rw [CFSGHermitianRangeIsometry.onRange_apply]
    change F.map p + (c⁻¹ • G.map) 0 = F.map p
    rw [map_zero,add_zero]
  · intro z
    dsimp only [A]
    rw [CFSGHermitianRangeIsometry.onRange_apply]
    change F.map 0 + c⁻¹ • G.map z = c⁻¹ • G.map z
    rw [map_zero,zero_add]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
