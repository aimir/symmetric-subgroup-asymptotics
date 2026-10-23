import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalParabolicAction

/-! An automorphism of the SAME original model fixing the actual
opposed Sylow pair fixes both positive minimal parabolics and both full
negative simple relative root groups. Their exact q versus q^3 orders
eliminate the potential type swap, including for q=2. No quotient
automorphism or root parameter map is assumed to lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootAction
open CFSGTrialityGeckOriginalNegativeRootCardinality CFSGTrialityGeckOriginalNegativeRootIntersection
open CFSGTrialityGeckOriginalParabolicAction CFSGTrialityGeckOriginalUpperNormalizer
open CFSGTrialityGeckOriginalOppositeAlignment CFSGTrialityGeckOriginalRootFamily

theorem original_pair_fixer_fixes_parabolics_and_negative_roots (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hU : (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)).map f.toMonoidHom=
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    (∀a:Bool,(originalSimpleParabolic q a).map f.toMonoidHom=originalSimpleParabolic q a) ∧
    (∀a:Bool,(originalNegativeOrbitRoot q a).map f.toMonoidHom=originalNegativeOrbitRoot q a) := by
  obtain ⟨sigma,hsigma⟩ := exists_original_parabolic_permutation q f hU
  have hroots (a:Bool) : (originalNegativeOrbitRoot q a).map f.toMonoidHom=
      originalNegativeOrbitRoot q (sigma a) := by
    rw [←original_negative_inf_simpleParabolic,Subgroup.map_inf _ _ _ f.injective,
      hV,hsigma a,original_negative_inf_simpleParabolic]
  have hfix (a:Bool) : sigma a=a := by
    have hc := Nat.card_congr ((originalNegativeOrbitRoot q a).equivMapOfInjective
      f.toMonoidHom f.injective).toEquiv
    rw [hroots a] at hc
    exact (originalNegativeOrbitRoot_card_injective q hc).symm
  constructor
  · intro a
    exact (hsigma a).trans (congrArg (originalSimpleParabolic q) (hfix a))
  · intro a
    exact (hroots a).trans (congrArg (originalNegativeOrbitRoot q) (hfix a))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootAction
