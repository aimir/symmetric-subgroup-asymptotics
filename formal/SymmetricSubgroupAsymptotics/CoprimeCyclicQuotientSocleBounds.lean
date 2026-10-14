import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles

/-!
# Arbitrary positive socle bounds in coprime cyclic extensions

The prime-primary part uses the actual bound on ambient normal subgroups
inside the original prime kernel. The complementary socle is cyclic, so
prime-type sharing gives `max t 1`, and hence `t` whenever `1 ≤ t`.
The original kernel image is retained in every surjective quotient.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace CoprimeCyclicQuotientSocleBounds

variable {G : Type} [Group G] [Finite G]

theorem socleBound_of_kernel (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    [IsCyclic (G ⧸ E)] (hcop : Nat.Coprime p (Nat.card (G ⧸ E)))
    (t : ℕ) (ht : 1 ≤ t)
    (hgen : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ t) :
    SocleNormalGeneratorBound G t := by
  have hprimary := hgen (minimalNormalSoclePart G (fun M ↦ IsPGroup p M))
    inferInstance (CoprimeCyclicQuotientSocles.primarySocle_le p E hcop)
  letI := CoprimeCyclicQuotientSocles.nonprimarySocle_isCyclic p E hE
  have hother := CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic
    (minimalNormalSoclePart G (fun M ↦ ¬ IsPGroup p M))
  apply (socleNormalGeneratorBound_iff_normalGen_le G t).2
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts p G).trans
    (max_le hprimary (hother.trans ht))

theorem image_normalGen_le {Q : Type} [Group Q] [Finite Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (E : Subgroup G) [E.Normal] (t : ℕ)
    (hgen : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ t)
    (H : Subgroup Q) [H.Normal] (hHE : H ≤ E.map pi) :
    MarkedC4.normalGen H ≤ t := by
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

/-- The same positive bound holds for every actual surjective image of
the original group, with no complement assumption on that image. -/
theorem quotientSocle_of_kernel (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    [IsCyclic (G ⧸ E)] (hcop : Nat.Coprime p (Nat.card (G ⧸ E)))
    (t : ℕ) (ht : 1 ≤ t)
    (hgen : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ t)
    {Q : Type} [Group Q] (pi : G →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q t := by
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
  apply socleBound_of_kernel p F (hE.map pi) hcopF t ht
  intro H hH hHF
  letI := hH
  exact image_normalGen_le pi hpi E t hgen H hHF

/-- The denominator remains an arbitrary original normal subgroup. -/
theorem quotient (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    [IsCyclic (G ⧸ E)] (hcop : Nat.Coprime p (Nat.card (G ⧸ E)))
    (t : ℕ) (ht : 1 ≤ t)
    (hgen : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ t)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) t :=
  quotientSocle_of_kernel p E hE hcop t ht hgen
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CoprimeCyclicQuotientSocleBounds
end SymmetricSubgroupAsymptotics

end
