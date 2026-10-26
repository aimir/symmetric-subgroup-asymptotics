import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryCentralReflection
import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedAmbientHom
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOuterWeylInvolution

/-! The recovered original reflection is the literal length-seven Weyl
word. Its intersection flag INSIDE the derived group is the restriction
of the ambient middle block, rather than an asserted internal C4. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryReflectionMiddleFlag
open CFSGReeFFourBinaryCentralReflection CFSGReeFFourBinaryPenultimateWeyl
open CFSGReeFFourPenultimateMiddleIntersection CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourInversionPeelingWords CFSGOpposedSubgroupPeelingChain
open CFSGReeFFourMinimalParabolics CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourSignedBlockGeneration
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourMiddleFixedSubgroup

private theorem step_eq_simple (m : ℕ) (head : Bool) (n : ℕ) :
    step m head n=simpleWeyl m (axis head n) := rfl

private theorem conjugate_alternating {G : Type*} [Group G] (a b : G)
    (ha : a^2=1) (hb : b^2=1) :
    ((a*b)^2)⁻¹*b*((a*b)^2)=b*(a*b)^4 := by
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right ((pow_two a).symm.trans ha)
  have hbi : b⁻¹=b := inv_eq_of_mul_eq_one_right ((pow_two b).symm.trans hb)
  simp only [pow_succ,pow_zero,mul_inv_rev,hai,hbi,inv_one,
    one_mul,mul_one,mul_assoc]

private theorem restricted_intersection {G : Type*} [Group G]
    (N U : Subgroup G) [N.Normal] (g : G) :
    U.comap N.subtype ⊓ (U.comap N.subtype).comap (MulAut.conjNormal g).toMonoidHom=
      (U⊓U.comap (MulAut.conj g).toMonoidHom).comap N.subtype := by
  ext x
  rfl

theorem fourth_prefix_word (m : ℕ) :
    wordPrefix (step m true) 4=(outerFixedWeyl m*middleFixedWeyl m)^2 := by
  change step m true 3*(step m true 2*(step m true 1*(step m true 0*1)))=_
  simp only [step_eq_simple]
  change simpleWeyl m false*(simpleWeyl m true*(simpleWeyl m false*
    (simpleWeyl m true*1)))=_
  rw [simpleWeyl_false,simpleWeyl_true]
  simp only [pow_two,mul_one,mul_assoc]

theorem centralReflection_eq_penultimate :
    centralReflection=shortModelWord 0 (13 : Fin 16) := by
  have ho := opposition_eq_simpleWeyl_power 0
  rw [simpleWeyl_false,simpleWeyl_true] at ho
  have hc : Commute (oppositionFixed 0) (middleFixedWeyl 0) := by
    simpa only [simpleWeyl_true] using binary_opposition_commute_simple true
  calc
    centralReflection=((outerFixedWeyl 0*middleFixedWeyl 0)^2)⁻¹*
      middleFixedWeyl 0*((outerFixedWeyl 0*middleFixedWeyl 0)^2) := by
        simp only [centralReflection,centralConjugator,fourth_prefix_word,inv_inv]
    _=middleFixedWeyl 0*(outerFixedWeyl 0*middleFixedWeyl 0)^4 :=
      conjugate_alternating _ _ (CFSGReeFFourFixedOuterWeylInvolution.outer_weyl_square 0)
        (middleWeyl_square 0)
    _=middleFixedWeyl 0*oppositionFixed 0 := congrArg (fun g => middleFixedWeyl 0*g) ho.symm
    _=oppositionFixed 0*middleFixedWeyl 0 := hc.eq.symm
    _=shortModelWord 0 (13 : Fin 16) := binary_short_thirteen_eq.symm

def reflectionIntersection : Subgroup (commutator (originalModelFixed 0)) :=
  derivedPositive 0 ⊓ (derivedPositive 0).comap
    (MulAut.conjNormal centralReflection).toMonoidHom

theorem reflectionIntersection_eq_restricted_middle :
    reflectionIntersection=(middleFixedSubgroup 0).comap
      (commutator (originalModelFixed 0)).subtype := by
  have h := restricted_intersection (commutator (originalModelFixed 0))
    (fixedPositive 0) centralReflection
  have hi : fixedPositive 0⊓(fixedPositive 0).comap
      (MulAut.conj centralReflection).toMonoidHom=middleFixedSubgroup 0 := by
    rw [centralReflection_eq_penultimate]
    exact penultimate_intersection_eq_middle 0
  exact h.trans (congrArg (fun U : Subgroup (originalModelFixed 0) =>
    U.comap (commutator (originalModelFixed 0)).subtype) hi)

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryReflectionMiddleFlag
