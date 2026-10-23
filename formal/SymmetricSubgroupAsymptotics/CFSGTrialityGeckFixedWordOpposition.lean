import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedWordSimpleSigns
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeOpposition

/-! Disjoint genuine fixed positive groups force the entire relative
Weyl conjugate to be the literal fixed negative group. Ambient sign
recognition is a conclusion from fixed tests, not an assumed larger
ambient disjointness statement. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedWordOpposition
open CFSGTrialityGeckFixedWordSimpleSigns CFSGTrialityGeckFixedPositiveRaw
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4NormTwo CFSGTrialityRelativeWordLanguage
open CFSGNormTwoCoordinateNegativeSimpleWord CFSGNormTwoGeckWeylWordDegree
open CFSGTrialityGeckMatrixTwist CFSGNormTwoGeckPositivePGroup
open CFSGCentralTwistedCommutatorLift CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private theorem fixed_conjugation_map {G : Type*} [Group G]
    (tau : MulAut G) (W : G) (hW : tau W=W) :
    (fixedSubgroup tau).map (MulAut.conj W).toMonoidHom=fixedSubgroup tau := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change tau (W*y*W⁻¹)=W*y*W⁻¹
    change tau y=y at hy
    rw [map_mul,map_mul,map_inv,hW,hy]
  · intro hx
    change tau x=x at hx
    refine ⟨W⁻¹*x*W,?_,?_⟩
    · change tau (W⁻¹*x*W)=W⁻¹*x*W
      rw [map_mul,map_mul,map_inv,hW,hx]
    · change W*(W⁻¹*x*W)*W⁻¹=x
      group

theorem fixedPositiveRaw_eq_signedFixed (q : CFSG.PrimePower) :
    fixedPositiveRaw q=signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) false := by
  ext x
  exact mem_fixedPositiveRaw_iff q x

theorem ambient_positive_image_eq_negative_of_fixed_disjoint (q : CFSG.PrimePower) (r : List Bool)
    (hdisj : fixedPositiveRaw q⊓(fixedPositiveRaw q).map
      (MulAut.conj (wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r))).toMonoidHom=⊥) :
    (Positive (q.Extension 3)).map
      (MulAut.conj (wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r))).toMonoidHom=
        rootGroup A hs hp Base Index (q.Extension 3) true :=
  positive_map_eq_negative_of_simple_nonpositive A hd hs hp ho (q.Extension 3) (expandRelative r)
    (relative_simple_nonpositive_of_fixed_disjoint q r hdisj)

theorem fixed_positive_image_eq_negative_of_disjoint (q : CFSG.PrimePower) (r : List Bool)
    (hdisj : fixedPositiveRaw q⊓(fixedPositiveRaw q).map
      (MulAut.conj (wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r))).toMonoidHom=⊥) :
    (fixedPositiveRaw q).map
      (MulAut.conj (wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r))).toMonoidHom=
        signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true := by
  rw [fixedPositiveRaw_eq_signedFixed]
  change ((Positive (q.Extension 3))⊓fixedSubgroup
      (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3))).map
    (MulAut.conj (wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r))).toMonoidHom=_
  rw [Subgroup.map_inf _ _ _ (MulAut.conj _).injective,
    ambient_positive_image_eq_negative_of_fixed_disjoint q r hdisj,
    fixed_conjugation_map _ _ (CFSGTrialityGeckFixedPositiveRaw.relative_word_fixed q r)]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedWordOpposition
