import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNormalizedPointDetermination

/-! A literal rank3/4 point permutation fixing its original opposed
planes is realized by a CONSTRUCTED linear similitude. The common mixed
ratio and the odd middle coefficient are both derived, not supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup

abbrev UnitaryLinearPointPieces (q : CFSG.PrimePower) (r : ℕ) (f : Equiv.Perm (UnitaryPoint q r)) : Prop :=
  ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r),
    Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f
      ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2)))

private theorem postcompose_cancel (q : CFSG.PrimePower) (r : ℕ)
    (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r))
    (f : Equiv.Perm (UnitaryPoint q r)) (R : UnitaryPoint q r) :
    singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g
      (unitarySimilitudePostcompose q r g f R) = f R := by
  change (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g)
    ((singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g⁻¹) (f R)) = f R
  rw [map_inv]
  exact (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g).apply_symm_apply (f R)

def unitaryRankFourMiddleSimilitude (q : CFSG.PrimePower) (c : q.Extension 2)
    (hc : c ≠ 0) (hcn : definingFieldAutomorphism q 2 c * c = 1) :
    similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4) :=
  ⟨unitaryRankFourMiddleScaleEquiv q c hc,1,one_ne_zero,by
    intro x y
    change unitaryNaturalPair q 4 (unitaryRankFourMiddleScale q c x) (unitaryRankFourMiddleScale q c y) =
      1 * unitaryNaturalPair q 4 x y
    rw [one_mul]
    exact unitaryRankFourMiddleScale_pair q c hcn x y⟩

theorem unitary_rankThree_opposed_fixed_realization (q : CFSG.PrimePower)
    (f : Equiv.Perm (UnitaryPoint q 3))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3) f)
    (hlinear : UnitaryLinearPointPieces q 3 f)
    (hfixP : ∀ R : UnitaryPoint q 3, R.val ≤ unitaryStandardSingularSpace q 3 → f R = R)
    (hfixZ : ∀ R : UnitaryPoint q 3, R.val ≤ unitaryOppositeSingularSpace q 3 → f R = R) :
    ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 3),
      ∀ R : UnitaryPoint q 3,
        f R = singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 3) g R := by
  obtain ⟨g,hP,hZ,hmixed⟩ := exists_unitary_lowRank_mixed_normalization q 0 (by decide) f hf hlinear hfixP hfixZ
  have hfix := unitary_rankThree_normalized_point_fix q (unitarySimilitudePostcompose q 3 g f)
    (unitarySimilitudePostcompose_preserves q 3 g f hf) hP hZ hmixed
  refine ⟨g,?_⟩
  intro R
  exact (postcompose_cancel q 3 g f R).symm.trans
    (congrArg (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 3) g) (hfix R))

theorem unitary_rankFour_opposed_fixed_realization (q : CFSG.PrimePower)
    (f : Equiv.Perm (UnitaryPoint q 4))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) f)
    (hlinear : UnitaryLinearPointPieces q 4 f)
    (hfixP : ∀ R : UnitaryPoint q 4, R.val ≤ unitaryStandardSingularSpace q 4 → f R = R)
    (hfixZ : ∀ R : UnitaryPoint q 4, R.val ≤ unitaryOppositeSingularSpace q 4 → f R = R) :
    ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4),
      ∀ R : UnitaryPoint q 4,
        f R = singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4) g R := by
  obtain ⟨g,hP,hZ,hmixed⟩ := exists_unitary_lowRank_mixed_normalization q 1 (by decide) f hf hlinear hfixP hfixZ
  have hlocal : UnitaryLinearPointPieces q 4 (unitarySimilitudePostcompose q 4 g f) := by
    intro M
    obtain ⟨F⟩ := hlinear M
    exact ⟨unitarySimilitudePostcompose_piece q 4 g f ⟨M.val,M.property.1⟩ F⟩
  obtain ⟨c,hc,hcn,hpoints⟩ := unitary_rankFour_normalized_point_middle q (unitarySimilitudePostcompose q 4 g f)
    (unitarySimilitudePostcompose_preserves q 4 g f hf) hlocal hP hZ hmixed
  let m := unitaryRankFourMiddleSimilitude q c hc hcn
  refine ⟨g*m,?_⟩
  intro R
  have hm : (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4) m R).val =
      R.val.map (unitaryRankFourMiddleScale q c) :=
    singularPointHom_val (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4) m R
  have hF : unitarySimilitudePostcompose q 4 g f R =
      singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4) m R :=
    Subtype.ext ((hpoints R).trans hm.symm)
  calc
    f R = singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4) g
      (unitarySimilitudePostcompose q 4 g f R) := (postcompose_cancel q 4 g f R).symm
    _ = singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4) g
      (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4) m R) := congrArg _ hF
    _ = singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4) (g*m) R :=
      (congrArg (fun e : Equiv.Perm (UnitaryPoint q 4) => e R)
        ((singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) 4)).map_mul g m)).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
