import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowRankPointFixedRatio
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHalfSimilitude

/-! Constructed inverse half-similitude normalization removes the
original common mixed-ray ratio. Orthogonality and the SAME identity
local pieces are transported explicitly at point-permutation level. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup

def unitarySimilitudePostcompose (q : CFSG.PrimePower) (r : ℕ)
    (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r))
    (f : Equiv.Perm (UnitaryPoint q r)) : Equiv.Perm (UnitaryPoint q r) :=
  singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g⁻¹ * f

theorem unitarySimilitudePostcompose_preserves (q : CFSG.PrimePower) (r : ℕ)
    (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r))
    (f : Equiv.Perm (UnitaryPoint q r))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f) :
    PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) (unitarySimilitudePostcompose q r g f) := by
  intro P Q
  exact (hermitian_similitude_point_preserves_orthogonality (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) r) g⁻¹ (f P) (f Q)).trans (hf P Q)

def unitarySimilitudePostcompose_piece (q : CFSG.PrimePower) (r : ℕ)
    (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r))
    (f : Equiv.Perm (UnitaryPoint q r))
    (S : IsotropicSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r))
    (F : SemilinearPiece (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f S (RingEquiv.refl (q.Extension 2))) :
    SemilinearPiece (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)
      (unitarySimilitudePostcompose q r g f) S (RingEquiv.refl (q.Extension 2)) :=
  hermitian_similitude_postcompose_piece (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) r) f S (RingEquiv.refl (q.Extension 2)) g⁻¹ F

theorem exists_unitary_lowRank_mixed_normalization (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : Equiv.Perm (UnitaryPoint q (s+3)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f)
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryStandardSingularSpace q (s+3) → f R = R)
    (hfixZ : ∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryOppositeSingularSpace q (s+3) → f R = R) :
    ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)),
      (∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryStandardSingularSpace q (s+3) →
        unitarySimilitudePostcompose q (s+3) g f R = R) ∧
      (∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryOppositeSingularSpace q (s+3) →
        unitarySimilitudePostcompose q (s+3) g f R = R) ∧
      ∀ (x y : Fin (s+4) → q.Extension 2),
        x ∈ unitaryStandardSingularSpace q (s+3) → x ≠ 0 → y ∈ unitaryOppositeSingularSpace q (s+3) → y ≠ 0 →
        unitaryNaturalPair q (s+3) y x = 0 → ∀ R : UnitaryPoint q (s+3), R.val = (q.Extension 2) ∙ (x+y) →
        unitarySimilitudePostcompose q (s+3) g f R = R := by
  obtain ⟨t,ht,htf,hratio⟩ := unitary_lowRank_point_opposed_common_fixed_ratio q s hs f hf hlinear hfixP hfixZ
  obtain ⟨u,hu,hun⟩ := exists_unitaryHalfScale_parameters q t ht htf
  let g := unitaryHalfSimilitude q (s+3) t u ht hu htf hun
  let k := singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)) g
  let l := singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)) g⁻¹
  have hcancel (R : UnitaryPoint q (s+3)) : l (k R) = R := by
    change (singularPointHom (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3)) g⁻¹) (k R) = R
    rw [map_inv]
    exact k.symm_apply_apply R
  refine ⟨g,?_,?_,?_⟩
  · intro R hR
    have hk : k R = R := unitaryHalfSimilitude_fix_standard_point q (s+3) t u ht hu htf hun R hR
    change l (f R) = R
    exact (congrArg l ((hfixP R hR).trans hk.symm)).trans (hcancel R)
  · intro R hR
    have hk : k R = R := unitaryHalfSimilitude_fix_opposite_point q (s+3) t u ht hu htf hun R hR
    change l (f R) = R
    exact (congrArg l ((hfixZ R hR).trans hk.symm)).trans (hcancel R)
  · intro x y hx hx0 hy hy0 hyx R hR
    have hsum0 : x+y ≠ 0 := by
      intro h
      have hxZ : x ∈ unitaryOppositeSingularSpace q (s+3) := by
        rw [add_eq_zero_iff_eq_neg.mp h]
        exact (unitaryOppositeSingularSpace q (s+3)).neg_mem hy
      exact hx0 ((Submodule.disjoint_def.mp (unitaryStandard_opposite_disjoint q (s+3))) x hx hxZ)
    have hmem : x+y ∈ R.val := by rw [hR]; exact Submodule.mem_span_singleton_self _
    have hn : unitaryNaturalPair q (s+3) (x+y) (x+y) = 0 := R.property.2 _ hmem
    have hRay : R = singularRay (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) (x+y) hsum0 hn := Subtype.ext hR
    have hfr : (f R).val = (q.Extension 2) ∙ (x+t • y) := by
      rw [hRay]
      exact hratio x y hx hx0 hy hy0 hyx hsum0 hn
    have hkr : (k R).val = (q.Extension 2) ∙ (x+t • y) :=
      unitaryHalfSimilitude_mixed_point q (s+3) t u ht hu htf hun x y hx hy R hR
    change l (f R) = R
    exact (congrArg l (Subtype.ext (hfr.trans hkr.symm))).trans (hcancel R)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
