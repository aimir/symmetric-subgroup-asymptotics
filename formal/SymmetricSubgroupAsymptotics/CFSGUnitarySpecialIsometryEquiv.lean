import SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianScalarCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRootLabels
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalSL

/-! Special isometries of the literal signed reversal are exactly the
already proved natural fixed elementary matrices. The equivalence is
constructed on the same matrix units; no named unitary recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGHermitianSimilitudeGroup CFSGTwistedAUnitaryParameters
open CFSGProjectiveLinearPointAction

def naturalFixedToHermitianIsometry (q : CFSG.PrimePower) (r : ℕ) :
    naturalFixed r q →* isometries (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) where
  toFun g := ⟨linearEquiv g.val.val, fun v w =>
    hermitianPair_isometry _ _ _ (naturalFixed_signedForm q r g) v w⟩
  map_one' := by apply Subtype.ext; exact map_one linearEquiv.toMonoidHom
  map_mul' g h := by apply Subtype.ext; exact map_mul linearEquiv.toMonoidHom g.val.val h.val.val

theorem naturalFixedToHermitianIsometry_matrix (q : CFSG.PrimePower) (r : ℕ)
    (g : naturalFixed r q) :
    isometryMatrixHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r)
      (naturalFixedToHermitianIsometry q r g) = g.val.val := by
  change linearEquiv.symm (linearEquiv g.val.val) = g.val.val
  exact linearEquiv.symm_apply_apply _

def naturalFixedToSpecialIsometry (q : CFSG.PrimePower) (r : ℕ) :
    naturalFixed r q →* specialIsometries (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r) :=
  (naturalFixedToHermitianIsometry q r).codRestrict _ (fun g => by
    apply Units.ext
    change Matrix.det (isometryMatrixHom (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r) (naturalFixedToHermitianIsometry q r g) :
        Mat (q.Extension 2) r) = 1
    rw [naturalFixedToHermitianIsometry_matrix]
    exact naturalElementary_det _ _ g.val)

theorem naturalFixedToSpecialIsometry_injective (q : CFSG.PrimePower) (r : ℕ) :
    Function.Injective (naturalFixedToSpecialIsometry q r) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg (fun e : specialIsometries (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r) =>
    isometryMatrixHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) e.val) he
  exact (naturalFixedToHermitianIsometry_matrix q r g).symm.trans
    (hh.trans (naturalFixedToHermitianIsometry_matrix q r h))

theorem naturalFixedToSpecialIsometry_surjective (q : CFSG.PrimePower) (r : ℕ) :
    Function.Surjective (naturalFixedToSpecialIsometry q r) := by
  intro e
  let sigma := definingFieldAutomorphism q 2
  let H := signedReversalUnit (q.Extension 2) r
  let A := isometryMatrixHom sigma H e.val
  have hdet : Matrix.det (A : Mat (q.Extension 2) r) = 1 :=
    congrArg (fun z : (q.Extension 2)ˣ => (z : q.Extension 2)) e.property
  let g : NaturalElementary (q.Extension 2) r := ⟨A, unit_mem_natural_of_det _ _ A hdet⟩
  have hp : ∀ v w, hermitianPair sigma H ((A : Mat (q.Extension 2) r) *ᵥ v)
      ((A : Mat (q.Extension 2) r) *ᵥ w) = hermitianPair sigma H v w := by
    intro v w
    change hermitianPair sigma H (linearEquiv (linearEquiv.symm e.val.val) v)
      (linearEquiv (linearEquiv.symm e.val.val) w) = _
    rw [linearEquiv.apply_symm_apply]
    exact e.val.property v w
  have hm := (CFSGHermitianMatrixPullback.similitude_matrix_iff sigma
    (H : Mat (q.Extension 2) r) (A : Mat (q.Extension 2) r) (1 : q.Extension 2)).mp
    (by simpa only [one_mul] using hp)
  rw [one_smul] at hm
  have hgfix : diagramFieldUnitHom (q.Extension 2) r sigma.toRingHom A = A :=
    unit_fixed_of_signedForm _ _ _ A hm
  let u : naturalFixed r q := ⟨g, hgfix⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply linearEquiv.symm.injective
  change linearEquiv.symm (linearEquiv A) = linearEquiv.symm e.val.val
  exact linearEquiv.symm_apply_apply A

def naturalFixedSpecialIsometryEquiv (q : CFSG.PrimePower) (r : ℕ) :
    naturalFixed r q ≃* specialIsometries (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r) :=
  MulEquiv.ofBijective (naturalFixedToSpecialIsometry q r)
    ⟨naturalFixedToSpecialIsometry_injective q r, naturalFixedToSpecialIsometry_surjective q r⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
