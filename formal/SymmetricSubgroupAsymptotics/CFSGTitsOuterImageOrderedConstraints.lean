import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterCentralizerLift
import SymmetricSubgroupAsymptotics.CFSGReeFFourOrderedTailMaskCoordinates
import SymmetricSubgroupAsymptotics.CFSGTitsDerivedCentralQuotientEquivalence
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionOuterWord

/-! Every literal pair-fixer image of x has a SAME original ordered
source satisfying the fixed involution/reflection/odd-product conditions.
All relations lift through the proved FULL quotient equivalence. This is
a necessary-condition theorem, not the finite three-code classification
or an evaluation-injectivity/outer-cardinality assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsOuterImageOrderedConstraints
open CFSGTitsIntrinsicOuterCentralizerLift CFSGTitsIntrinsicOuterCentralizer
open CFSGTitsIntrinsicMiddleRadical CFSGTitsAmbientPairAlignment
open CFSGReeFFourOrderedTailMaskCoordinates CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryOrderedRootWords CFSGFFourNormPrimeFieldWords
open CFSGReeFFourOppositionOuterWord CFSGReeFFourSignedOuterOddProduct
open CFSGTitsDerivedCentralQuotientEquivalence CFSGTitsMiddleWeylRecovery
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourOuterThreeWord
open CFSGReeFFourOuterCentralizingReflection CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourAmbientCentralQuotientAction
private abbrev D := commutator (originalModelFixed 0)
private abbrev opposite : MulAut D := MulAut.conjNormal (oppositionFixed 0)

private theorem outer_square : (originalOuterRoot 0)^2=1 := by
  have hs : (derivedOuterRoot 0)^2=1 := Subtype.ext (outerInvolution_square 0)
  exact (map_pow (derivedReeHom 0) (derivedOuterRoot 0) 2).symm.trans
    ((congrArg (derivedReeHom 0) hs).trans (map_one (derivedReeHom 0)))

private theorem outer_ne_one : originalOuterRoot 0≠1 := by
  intro hx
  have hn : negativeOriginalOuterRoot 0=1 := by
    simp only [negativeOriginalOuterRoot,hx,mul_one,mul_inv_cancel]
  have h := negative_mul_positive_order 0
  rw [hn,hx,one_mul,orderOf_one] at h
  exact (by decide : (1 : ℕ)≠3) h

private theorem odd_product_ne_one {G : Type*} [Group G] (g : G)
    (hg : orderOf g=3) : g≠1 := by
  intro h
  rw [h,orderOf_one] at hg
  exact (by decide : (1 : ℕ)≠3) hg

private theorem pair_image_square (f : pairStabilizer) :
    (f.val (originalOuterRoot 0))^2=1 :=
  (map_pow f.val.toMonoidHom (originalOuterRoot 0) 2).symm.trans
    ((congrArg f.val outer_square).trans (map_one f.val))

private theorem pair_image_ne_one (f : pairStabilizer) : f.val (originalOuterRoot 0)≠1 :=
  fun h=>outer_ne_one (f.val.injective (h.trans (map_one f.val).symm))

private theorem fixed_odd_order {G : Type*} [Group G] (F : MulAut G) (o x : G)
    (ho : F o=o) (hx : orderOf ((o*x*o⁻¹)*x)=3) :
    orderOf ((o*F x*o⁻¹)*F x)=3 := by
  have hv : F ((o*x*o⁻¹)*x)=(o*F x*o⁻¹)*F x := by
    rw [map_mul,map_mul,map_mul,map_inv,ho]
  exact (congrArg orderOf hv).symm.trans
    ((orderOf_injective F.toMonoidHom F.injective _).trans hx)

private theorem pair_image_odd_order (f : pairStabilizer) :
    orderOf ((oppositionRoot*f.val (originalOuterRoot 0)*oppositionRoot⁻¹)*
      f.val (originalOuterRoot 0))=3 :=
  fixed_odd_order f.val oppositionRoot (originalOuterRoot 0)
    (pairStabilizer_fixes_oppositionRoot f) intrinsic_opposition_outer_product_order

private theorem opposite_map (u : D) :
    derivedReeHom 0 (opposite u)=oppositionRoot*derivedReeHom 0 u*oppositionRoot⁻¹ := by
  have ha : derivedReeHom 0 (opposite u)=
      ambientAction 0 (oppositionFixed 0) (derivedReeHom 0 u) :=
    (ambientAction_apply 0 (oppositionFixed 0) u).symm
  have hb := congrArg (fun F : MulAut CFSG.Models.Tits=>F (derivedReeHom 0 u))
    oppositionRoot_action
  exact ha.trans hb.symm

private theorem map_opposite_product {G H : Type*} [Group G] [Group H]
    (f : G→*H) (A : MulAut G) (o : H)
    (hA : ∀u,f (A u)=o*f u*o⁻¹) (u : G) (x : H) (hu : f u=x) :
    f (A u*u)=(o*x*o⁻¹)*x := by
  rw [map_mul,hA,hu]

private theorem lift_conditions {G H : Type*} [Group G] [Group H]
    (f : G→*H) (hf : Function.Injective f) (A : MulAut G) (o : H)
    (hA : ∀u,f (A u)=o*f u*o⁻¹) (u : G) (x : H) (hu : f u=x)
    (hx : x≠1) (hs : x^2=1) (hp : orderOf ((o*x*o⁻¹)*x)=3) :
    u≠1 ∧ u^2=1 ∧ A u*u≠1 ∧ (A u*u)^3=1 := by
  have hprod : f (A u*u)=(o*x*o⁻¹)*x := map_opposite_product f A o hA u x hu
  have hne := odd_product_ne_one ((o*x*o⁻¹)*x) hp
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    exact hx (hu.symm.trans ((congrArg f h).trans (map_one f)))
  · apply hf
    rw [map_pow,hu,hs,map_one]
  · intro h
    exact hne (hprod.symm.trans ((congrArg f h).trans (map_one f)))
  · apply hf
    rw [map_pow,hprod,map_one]
    rw [←hp]
    exact pow_orderOf_eq_one _

private theorem source_conditions (f : pairStabilizer) (u : D)
    (hu : derivedReeHom 0 u=f.val (originalOuterRoot 0)) :
    u≠1 ∧ u^2=1 ∧ opposite u*u≠1 ∧ (opposite u*u)^3=1 :=
  lift_conditions (G := D) (H := CFSG.Models.Tits)
    (derivedReeHom 0) derivedReeHom_injective opposite oppositionRoot opposite_map
    u (f.val (originalOuterRoot 0)) hu (pair_image_ne_one f) (pair_image_square f)
    (pair_image_odd_order f)

theorem exists_source_mask (f : pairStabilizer) :
    ∃u : sourceIntersection,∃c : Fin 1024,
      derivedReeHom 0 u.val=f.val (originalOuterRoot 0) ∧
      wordValue (Field 0) (orderedLetters (exponentFunction (tailBits c)) 8)=u.val.val.val ∧
      u.val≠1 ∧ u.val^2=1 ∧
      Commute (reflectionWord 0) u.val.val ∧
      opposite u.val*u.val≠1 ∧ (opposite u.val*u.val)^3=1 := by
  obtain ⟨u,hu,a,hfirst,ha,hcomm⟩ := exists_original_commuting_parameters
    (f.val (originalOuterRoot 0)) (pairStabilizer_outer_image_mem_flag f)
  have h0 : parameterBits a 0=false := by
    change decide ((a 0).val%2=1)=false
    rw [hfirst]
    rfl
  have h1 : parameterBits a 1=false := by
    change decide (2≤(a 0).val)=false
    rw [hfirst]
    rfl
  obtain ⟨c,hc⟩ := exists_code (parameterBits a) h0 h1
  have hw : wordValue (Field 0) (orderedLetters (exponentFunction (tailBits c)) 8)=u.val.val.val := by
    rw [hc]
    exact (encoded_word_value a).trans
      (congrArg (fun g : originalModelFixed 0=>g.val) ha.symm)
  have hsource := source_conditions f u.val hu
  have hcommu : Commute (reflectionWord 0) u.val.val :=
    Eq.mpr (congrArg (fun z : originalModelFixed 0=>Commute (reflectionWord 0) z) ha) hcomm
  exact ⟨u,c,hu,hw,hsource.1,hsource.2.1,hcommu,hsource.2.2.1,hsource.2.2.2⟩

end SymmetricSubgroupAsymptotics.CFSGTitsOuterImageOrderedConstraints
