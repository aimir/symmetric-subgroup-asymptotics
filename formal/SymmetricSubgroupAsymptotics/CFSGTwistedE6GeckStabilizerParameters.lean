import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalFieldAgreement
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalParameterFaithful
import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusParameters
import SymmetricSubgroupAsymptotics.CFSGTwoFieldSemilinearCosetIndex
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyStabilizer

/-! The actual opposed-Sylow stabilizer has faithful compatible
semilinear simple-parameter data. Both the field formula and faithfulness
are proved on the original group; no automorphism is lifted to J. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckStabilizerParameters
open CFSGSubgroupFamilyStabilizer CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGTwistedE6GeckOriginalFieldAgreement CFSGTwistedE6GeckOriginalParameterFaithful
open CFSGTwistedE6GeckOriginalSingletonA2 CFSGE6GeckRelativeScalarTuples
open CFSGE6GeckProductTorusParameters CFSGTwoFieldSemilinearCosetIndex
open CFSGSerreOrdinaryTwists

def pairStabilizer (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Subgroup (MulAut (CFSG.Models.TwistedE6 q)) :=
  familyStabilizer (fun neg : Bool => if neg then originalNegative q
    else (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))

theorem pair_preserves_positive (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (f : pairStabilizer q) :
    (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.val.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) := f.property false

theorem pair_preserves_negative (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (f : pairStabilizer q) : (originalNegative q).map f.val.toMonoidHom=originalNegative q :=
  f.property true

theorem parameters_faithful (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (f g : pairStabilizer q)
    (hp : ∀j a,f.val (pairedOriginalHom q false j (Multiplicative.ofAdd a))=
      g.val (pairedOriginalHom q false j (Multiplicative.ofAdd a)))
    (hs : ∀j a,f.val (singletonOriginalHom q false j (Multiplicative.ofAdd a))=
      g.val (singletonOriginalHom q false j (Multiplicative.ofAdd a))) : f=g := by
  apply inv_mul_eq_one.mp
  apply Subtype.ext
  apply eq_one_of_positive_simple_parameters_fixed q (f⁻¹*g).val
    (pair_preserves_positive q (f⁻¹*g)) (pair_preserves_negative q (f⁻¹*g))
  · intro j a
    change f.val.symm (g.val (pairedOriginalHom q false j (Multiplicative.ofAdd a)))=_
    rw [←hp j a]
    exact f.val.symm_apply_apply _
  · intro j a
    change f.val.symm (g.val (singletonOriginalHom q false j (Multiplicative.ofAdd a)))=_
    rw [←hs j a]
    exact f.val.symm_apply_apply _

theorem exists_semilinear_parameters (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : pairStabilizer q) :
    ∃ (s : compatibleFields (Coefficient q).subtype)
      (c : relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)),
      (∀j a,f.val (pairedOriginalHom q false j (Multiplicative.ofAdd a))=
        pairedOriginalHom q false j (Multiplicative.ofAdd ((pairedScaleHom _ _ c j : q.Extension 2)*s.val.1 a))) ∧
      (∀j a,f.val (singletonOriginalHom q false j (Multiplicative.ofAdd a))=
        singletonOriginalHom q false j (Multiplicative.ofAdd ((singletonScaleHom _ _ c j : Coefficient q)*s.val.2 a))) := by
  obtain ⟨tau,kap,c,d,e,h,hc,hd,he,hh,hagree,hpair,hsingle⟩ :=
    exists_compatible_positive_fields q f.val (pair_preserves_positive q f) (pair_preserves_negative q f)
  refine ⟨⟨(tau,kap),hagree⟩,scalarTuple _ _ (coefficient_involutive q)
    (Units.mk0 c hc) (Units.mk0 d hd) (Units.mk0 h hh) (Units.mk0 e he),?_,?_⟩
  · intro j a
    fin_cases j
    · exact (hpair a).1
    · exact (hpair a).2
  · intro j a
    fin_cases j
    · exact (hsingle a).1
    · exact (hsingle a).2

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckStabilizerParameters
