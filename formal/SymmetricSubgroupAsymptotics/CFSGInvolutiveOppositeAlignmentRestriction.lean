import SymmetricSubgroupAsymptotics.CFSGInvolutiveTwoGroupFixedIntersection
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality
import SymmetricSubgroupAsymptotics.CFSGConjugateComap

/-! Opposite alignment descends to a literal involution-fixed subgroup
of a finite group when positives are 2-groups and the positive action on
opposites is free. Existence of the ambient alignment is an explicit
input; the conjugator's fixedness is proved by uniqueness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInvolutiveOppositeAlignmentRestriction
open CFSGInvolutiveTwoGroupFixedIntersection CFSGSubgroupConjugateRestriction
open CFSGSubgroupConjugateOrbitCardinality CFSGConjugateComap
variable {G : Type*} [Group G]

theorem positive_conjugator_unique (P Q : Subgroup G)
    (hPN : P⊓Subgroup.normalizer (Q : Set G)=⊥)
    (b c : G) (hb : b∈P) (hc : c∈P)
    (he : Q.map (MulAut.conj b).toMonoidHom=Q.map (MulAut.conj c).toMonoidHom) : b=c := by
  have hconj : Q.map (MulAut.conj (b⁻¹*c)).toMonoidHom=Q := by
    rw [conjugate_mul,←he,←conjugate_mul,inv_mul_cancel]
    exact conjugate_eq_of_mem_normalizer Q 1 (Subgroup.one_mem _)
  have hn : b⁻¹*c∈Subgroup.normalizer (Q : Set G) :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mpr
      (congrArg (fun R : Subgroup G=>(R : Set G)) hconj)
  have hh : b⁻¹*c∈P⊓Subgroup.normalizer (Q : Set G) :=
    ⟨P.mul_mem (P.inv_mem hb) hc,hn⟩
  rw [hPN,Subgroup.mem_bot] at hh
  exact inv_mul_eq_one.mp hh

theorem fixed_opposite_alignment [Finite G]
    (P Q F : Subgroup G) (hP : IsPGroup 2 P) (tau : MulAut G)
    (hinv : Function.Involutive tau)
    (hPmap : P.map tau.toMonoidHom=P) (hQmap : Q.map tau.toMonoidHom=Q)
    (hF : ∀x,x∈F↔tau x=x)
    (hPN : P⊓Subgroup.normalizer (Q : Set G)=⊥)
    (halign : ∀g : G,P⊓P.map (MulAut.conj g).toMonoidHom=⊥→
      ∃b∈P,P.map (MulAut.conj g).toMonoidHom=Q.map (MulAut.conj b).toMonoidHom)
    (g : F) (hdisj : P.comap F.subtype⊓(P.comap F.subtype).map
      (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈P.comap F.subtype,(P.comap F.subtype).map (MulAut.conj g).toMonoidHom=
      (Q.comap F.subtype).map (MulAut.conj b).toMonoidHom := by
  have hstable (x : G) (hx : x∈P) : tau x∈P :=
    hPmap ▸ (show tau x∈P.map tau.toMonoidHom from ⟨x,hx,rfl⟩)
  have hd := inf_conjugate_eq_bot_of_fixed P F hP tau.toMonoidHom hinv hstable hF g hdisj
  obtain ⟨b,hb,he⟩ := halign g.val hd
  have htb : tau b∈P := hstable b hb
  have hg : tau g.val=g.val := (hF g.val).mp g.property
  have ht := congrArg (fun R : Subgroup G=>R.map tau.toMonoidHom) he
  simp only [map_conjugate,hPmap,hQmap] at ht
  change P.map (MulAut.conj (tau g.val)).toMonoidHom=
    Q.map (MulAut.conj (tau b)).toMonoidHom at ht
  rw [hg] at ht
  have hbfix : tau b=b :=
    (positive_conjugator_unique P Q hPN b (tau b) hb htb (he.symm.trans ht)).symm
  let B : F := ⟨b,(hF b).mpr hbfix⟩
  have hh := congrArg (fun R : Subgroup G=>R.comap F.subtype) he
  change (P.map (MulAut.conj (F.subtype g)).toMonoidHom).comap F.subtype=
    (Q.map (MulAut.conj (F.subtype B)).toMonoidHom).comap F.subtype at hh
  rw [comap_conjugate,comap_conjugate] at hh
  exact ⟨B,hb,hh⟩

end SymmetricSubgroupAsymptotics.CFSGInvolutiveOppositeAlignmentRestriction
