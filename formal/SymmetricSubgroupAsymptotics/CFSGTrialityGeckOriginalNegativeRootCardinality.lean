import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootIntersection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalCentralKernel
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroups

/-! Exact orders of the intrinsic negative relative root groups in the
SAME original model. The central quotient is injective on these genuine
p-subgroups, as proved from its actual positive Sylow injection. The
orders q^3 and q distinguish the two types even at q=2. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootCardinality
open CFSGTrialityGeckOriginalNegativeRootIntersection
open CFSGTrialityGeckNegativeParabolicRootIntersection CFSGTrialityGeckNegativeOrbitRootGroups
open CFSGTrialityGeckFixedOrbitRootGroups CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckGeneratedOriginalCentralKernel CFSGTrialityGeckGeneratedPositiveSylow
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckSimpleOrbitFlags CFSGTrialityGeckDiagramCovariance
open CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

private theorem injective_subtype_of_eq {G H : Type*} [Group G] [Group H]
    (f : G→*H) (P Q : Subgroup G) (he : P=Q)
    (hinj : Function.Injective (f.comp Q.subtype)) : Function.Injective (f.comp P.subtype) := by
  subst P
  exact hinj

theorem fixedOrbitNegative_card (q : CFSG.PrimePower) (a : Bool) :
    Nat.card (fixedOrbitNegative q a)=if a then q.order else q.order^3 := by
  let e := MulAut.conj (canonicalWord rawData (q.Extension 3) (orbitWord a))
  have hh := (Nat.card_congr ((fixedOrbitRootGroup q a).equivMapOfInjective
    e.toMonoidHom e.injective).toEquiv).symm
  change Nat.card ((fixedOrbitRootGroup q a).map
    (MulAut.conj (canonicalWord rawData (q.Extension 3) (orbitWord a))).toMonoidHom)=
      Nat.card (fixedOrbitRootGroup q a) at hh
  rw [fixedOrbitRootGroup_map] at hh
  rw [hh]
  cases a
  · exact fixedOrbitRootGroup_short_card q
  · exact fixedOrbitRootGroup_middle_card q

theorem negativeOrbitRootGenerated_card (q : CFSG.PrimePower) (a : Bool) :
    Nat.card (negativeOrbitRootGenerated q a)=if a then q.order else q.order^3 := by
  have hle : fixedOrbitNegative q a≤
      fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := by
    rw [←fixed_negative_inf_simpleParabolic q a]
    exact inf_le_left.trans (signedFixed_le_generated _ _ true)
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans
    (fixedOrbitNegative_card q a)

theorem originalNegativeOrbitRoot_card (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (a : Bool) :
    Nat.card (originalNegativeOrbitRoot q a)=if a then q.order else q.order^3 := by
  have hle : negativeOrbitRootGenerated q a≤
      rootPart (q.Extension 3) (definingFieldAutomorphism q 3) true := by
    rw [←negative_rootPart_inf_parabolicGenerated q a]
    exact inf_le_left
  have hN := (rootPart_isPGroup (q.Extension 3)
    (definingFieldAutomorphism q 3) q.prime true).to_le hle
  have hpinj : Function.Injective ((generatedToOriginal q).comp
      (generatedPositiveSylow q : Subgroup
        (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))).subtype) := by
    exact injective_subtype_of_eq (generatedToOriginal q) _ _
      (generatedPositiveSylow_coe q) (rootPart_positive_original_injective q)
  exact (CFSGCentralKernelPElements.p_subgroup_card_map (generatedToOriginal q)
    (generatedPositiveSylow q) hpinj (generatedToOriginal_kernel_le_center q)
    (negativeOrbitRootGenerated q a) hN).trans (negativeOrbitRootGenerated_card q a)

theorem originalNegativeOrbitRoot_card_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Function.Injective (fun a:Bool=>Nat.card (originalNegativeOrbitRoot q a)) := by
  have hq : 1<q.order := lt_of_lt_of_le (by decide : 1<2)
    (q.prime_isPrime.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime))
  have hlt : q.order<q.order^3 := by
    simpa only [pow_one] using pow_lt_pow_right₀ hq (by decide : (1:ℕ)<3)
  intro a b he
  dsimp only at he
  rw [originalNegativeOrbitRoot_card,originalNegativeOrbitRoot_card] at he
  cases a <;> cases b
  · rfl
  · exact False.elim ((ne_of_gt hlt) he)
  · exact False.elim ((ne_of_lt hlt) he)
  · rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootCardinality
