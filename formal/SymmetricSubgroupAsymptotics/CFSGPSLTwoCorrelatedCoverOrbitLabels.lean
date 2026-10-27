import SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverProjection
import SymmetricSubgroupAsymptotics.FiniteActionFibreBurnside

/-! Complete subset labels for orbits in ONE correlated G/H cover. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverOrbitLabels
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates CFSGPSLTwoProductTorusCover
open CFSGPSLTwoCorrelatedCoverProjection CFSGPSLTwoCorrelatedCoverMaskRepresentatives
variable {F J : Type*} [Field F] [Finite J]

def orbitLabels (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3) :
    MulAction.orbitRel.Quotient (J → projectiveBorel (F:=F)) (Cover H) ≃ Set J := by
  have hsurj : Function.Surjective (label H) := by
    intro s
    exact ⟨QuotientGroup.mk (weylMask (F:=F) s),label_mask H s⟩
  have hfibre (x y : Cover H) (hxy : label H x=label H y) :
      ∃ b : J → projectiveBorel (F:=F), b • y=x := by
    induction x using Quotient.inductionOn' with
    | h g =>
      induction y using Quotient.inductionOn' with
      | h k =>
        obtain ⟨s,b,hg⟩ := every_coset_has_mask_representative H hindex hcop g
        obtain ⟨t,c,hk⟩ := every_coset_has_mask_representative H hindex hcop k
        have hs : label H (QuotientGroup.mk g)=s := by
          rw [hg]
          change label H (b • QuotientGroup.mk (weylMask s))=s
          rw [label_invariant,label_mask]
        have ht : label H (QuotientGroup.mk k)=t := by
          rw [hk]
          change label H (c • QuotientGroup.mk (weylMask t))=t
          rw [label_invariant,label_mask]
        have hst : s=t := hs.symm.trans (hxy.trans ht)
        have hb : b • (QuotientGroup.mk (weylMask s) : Cover H)=QuotientGroup.mk g := hg.symm
        have hk' : (QuotientGroup.mk k : Cover H) =
            QuotientGroup.mk (borelPowerHom c*weylMask s) := by
          rw [hst]
          exact hk
        have hc : c • (QuotientGroup.mk (weylMask s) : Cover H)=QuotientGroup.mk k := hk'.symm
        refine ⟨b*c⁻¹,?_⟩
        change (b*c⁻¹) • (QuotientGroup.mk k : Cover H)=QuotientGroup.mk g
        rw [mul_smul,←hc,inv_smul_smul,hb]
  exact FiniteActionFibreBurnside.orbitQuotientEquiv (label H) hsurj
    (label_invariant H) hfibre

theorem orbitLabels_mk (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3) (q : Cover H) :
    orbitLabels H hindex hcop (Quotient.mk _ q) = label H q := rfl

end SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverOrbitLabels
