import SymmetricSubgroupAsymptotics.NonPrimeAbelianSoclePart
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Quotient socles for a prime kernel and a coprime cyclic quotient

Suppose every ambient normal subgroup contained in a normal p-kernel has
one ambient normal generator. This property passes to the actual kernel
image in every surjective quotient. The p-primary socle lies in that
image. The complementary socle embeds in the cyclic quotient, hence is
cyclic, and the two prime types share one normal-generator position.

The elementary-module theorem supplying the kernel hypothesis is kept
separate. No subgroup census or assumption about a final quotient socle
is part of this group-theoretic argument.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace CoprimeCyclicQuotientSocles

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalGen_le_one_of_isCyclic (H : Subgroup G) [H.Normal] [IsCyclic H] :
    MarkedC4.normalGen H ≤ 1 := by
  obtain ⟨g, hg⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic H)
  apply normalGen_le_of_fin_tuple (fun _ : Fin 1 ↦ g)
  have hrange : Set.range (fun _ : Fin 1 ↦ g) = {g} := by ext x; simp
  rw [hrange]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [← hg]
    exact Subgroup.mem_zpowers g
  · rw [← hg, Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_le_normalClosure

omit [Finite G] in
theorem quotientRestriction_injective (E H : Subgroup G) [E.Normal]
    (hinf : H ⊓ E = ⊥) :
    Function.Injective ((QuotientGroup.mk' E).comp H.subtype) := by
  apply (injective_iff_map_eq_one ((QuotientGroup.mk' E).comp H.subtype)).2
  intro x hx
  apply Subtype.ext
  apply Subgroup.mem_bot.mp
  rw [← hinf]
  exact ⟨x.property, (QuotientGroup.eq_one_iff x.val).mp hx⟩

theorem primarySocle_le (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal]
    (hcop : Nat.Coprime p (Nat.card (G ⧸ E))) :
    minimalNormalSoclePart G (fun M ↦ IsPGroup p M) ≤ E := by
  apply minimalNormalSoclePart_le_of
  intro M _hM hMp
  let q := QuotientGroup.mk' E
  have himage : IsPGroup p (M.map q) := hMp.map q
  obtain ⟨d, hd⟩ := himage.exists_card_eq
  have hdiv : Nat.card (M.map q) ∣ Nat.card (G ⧸ E) :=
    (M.map q).card_subgroup_dvd_card
  have hcard : Nat.card (M.map q) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hcop.pow_left d) (hd ▸ dvd_rfl) hdiv
  have hbot : M.map q = ⊥ := (Subgroup.card_eq_one).mp hcard
  have hker := (Subgroup.map_eq_bot_iff (H := M) (f := q)).mp hbot
  simpa only [q, QuotientGroup.ker_mk'] using hker

theorem nonprimarySocle_isCyclic (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    [IsCyclic (G ⧸ E)] :
    IsCyclic (minimalNormalSoclePart G (fun M ↦ ¬ IsPGroup p M)) := by
  let H := minimalNormalSoclePart G (fun M ↦ ¬ IsPGroup p M)
  have hcomm (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
      (hnot : ¬ IsPGroup p M) : IsMulCommutative M := by
    letI : M.Normal := hM.1
    have hinf : M ⊓ E = ⊥ := by
      by_contra hne
      have heq : M ⊓ E = M := hM.2.2 _ inferInstance hne inf_le_left
      have hME : M ≤ E := by rw [← heq]; exact inf_le_right
      exact hnot (hE.to_le hME)
    letI : IsCyclic M := isCyclic_of_injective
      ((QuotientGroup.mk' E).comp M.subtype) (quotientRestriction_injective E M hinf)
    infer_instance
  have hH : H = minimalNormalSoclePart G
      (fun M ↦ ¬ IsPGroup p M ∧ IsMulCommutative M) := by
    apply minimalNormalSoclePart_congr
    intro M hM
    exact ⟨fun hnot ↦ ⟨hnot, hcomm M hM hnot⟩, And.left⟩
  have hinf : H ⊓ E = ⊥ := by
    rw [hH]
    exact abelianNonPrimarySoclePart_inf_isPGroup_eq_bot p E hE
  exact isCyclic_of_injective ((QuotientGroup.mk' E).comp H.subtype)
    (quotientRestriction_injective E H hinf)

theorem socleBound_of_kernel (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    [IsCyclic (G ⧸ E)] (hcop : Nat.Coprime p (Nat.card (G ⧸ E)))
    (hgen : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ 1) :
    SocleNormalGeneratorBound G 1 := by
  have hprimary := hgen (minimalNormalSoclePart G (fun M ↦ IsPGroup p M))
    inferInstance (primarySocle_le p E hcop)
  letI := nonprimarySocle_isCyclic p E hE
  have hother := normalGen_le_one_of_isCyclic
    (minimalNormalSoclePart G (fun M ↦ ¬ IsPGroup p M))
  apply (socleNormalGeneratorBound_iff_normalGen_le G 1).2
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts p G).trans
    (max_le hprimary hother)

theorem image_normalGen_le_one {Q : Type} [Group Q] [Finite Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (E : Subgroup G) [E.Normal]
    (hgen : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ 1)
    (H : Subgroup Q) [H.Normal] (hHE : H ≤ E.map pi) :
    MarkedC4.normalGen H ≤ 1 := by
  let L : Subgroup G := E ⊓ H.comap pi
  have hL : L.map pi = H := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hHE hy
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have hbound := hgen L inferInstance inf_le_left
  rw [← hL]
  exact (MarkedC4.normalGen_map_le pi hpi L).trans hbound

/-- The actual image of the original kernel controls every original
surjective quotient. Neither quotient's normal subgroups are enumerated. -/
theorem quotientSocle_of_kernel (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    [IsCyclic (G ⧸ E)] (hcop : Nat.Coprime p (Nat.card (G ⧸ E)))
    (hgen : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ 1)
    {Q : Type} [Group Q] (pi : G →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 1 := by
  letI : Finite Q := Finite.of_surjective pi hpi
  let F := E.map pi
  letI : F.Normal := (inferInstance : E.Normal).map pi hpi
  let f : G ⧸ E →* Q ⧸ F :=
    QuotientGroup.map E F pi (Subgroup.le_comap_map pi E)
  have hf : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective E F pi
      ((QuotientGroup.mk'_surjective F).comp hpi) (Subgroup.le_comap_map pi E)
  letI : IsCyclic (Q ⧸ F) := isCyclic_of_surjective f hf
  have hcopF : Nat.Coprime p (Nat.card (Q ⧸ F)) :=
    hcop.of_dvd_right (Subgroup.card_dvd_of_surjective f hf)
  apply socleBound_of_kernel p F (hE.map pi) hcopF
  intro H hH hHF
  letI := hH
  exact image_normalGen_le_one pi hpi E hgen H hHF

end CoprimeCyclicQuotientSocles
end SymmetricSubgroupAsymptotics

end
