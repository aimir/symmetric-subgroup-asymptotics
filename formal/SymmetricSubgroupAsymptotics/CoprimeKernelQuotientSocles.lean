import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineSocleGenerators
import SymmetricSubgroupAsymptotics.NonPrimarySocleCoprimeQuotient
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocleBounds

/-! Socle bounds for a normal p-kernel and an arbitrary coprime quotient.
The kernel-contained and quotient normal-generator bounds combine by a
maximum, not a sum. The original kernel image is retained in each actual
surjective quotient. No cyclicity, splitting, or solubility is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace CoprimeKernelQuotientSocles

variable {G : Type} [Group G] [Finite G]

theorem socleBound_of_kernel (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    (hcop : Nat.Coprime p (Nat.card (G ⧸ E))) (t a : ℕ)
    (hkernel : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ t)
    (hquotient : ∀ K : Subgroup (G ⧸ E), K.Normal → MarkedC4.normalGen K ≤ a) :
    SocleNormalGeneratorBound G (max t a) := by
  have hp := hkernel (minimalNormalSoclePart G (fun M ↦ IsPGroup p M))
    inferInstance (CoprimeCyclicQuotientSocles.primarySocle_le p E hcop)
  let H := minimalNormalSoclePart G (fun M ↦ ¬ IsPGroup p M)
  have hinf : H ⊓ E = ⊥ :=
    NonPrimarySocleCoprimeQuotient.nonprimarySocle_inf_kernel_eq_bot p E hE hcop
  have himage : MarkedC4.normalGen H ≤
      MarkedC4.normalGen (H.map (QuotientGroup.mk' E)) := by
    simpa only [hinf, MarkedC4.normalGen_bot, zero_add] using
      MarkedC4.normalGen_normal_le_inter_add_image H E
  have hHnormal : (H.map (QuotientGroup.mk' E)).Normal :=
    (inferInstance : H.Normal).map _ (QuotientGroup.mk'_surjective E)
  have hother := himage.trans (hquotient _ hHnormal)
  apply (socleNormalGeneratorBound_iff_normalGen_le G (max t a)).2
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts p G).trans
    (max_le_max hp hother)

/-- Uniform ambient normal-generator bounds descend under a surjection. -/
theorem normalGen_image_bound {H Q : Type} [Group H] [Finite H]
    [Group Q] [Finite Q] (f : H →* Q) (hf : Function.Surjective f)
    (a : ℕ) (hgen : ∀ K : Subgroup H, K.Normal → MarkedC4.normalGen K ≤ a)
    (K : Subgroup Q) [K.Normal] : MarkedC4.normalGen K ≤ a := by
  have hpre := hgen (K.comap f) inferInstance
  have hm := (MarkedC4.normalGen_map_le f hf (K.comap f)).trans hpre
  simpa only [Subgroup.map_comap_eq_self_of_surjective hf K] using hm

/-- The bound applies to every actual surjective image, retaining pi(E).
The quotient bound is transferred from the original G/E, not re-assumed
on the image. -/
theorem socle_of_surjective (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    (hcop : Nat.Coprime p (Nat.card (G ⧸ E))) (t a : ℕ)
    (hkernel : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ t)
    (hquotient : ∀ K : Subgroup (G ⧸ E), K.Normal → MarkedC4.normalGen K ≤ a)
    {Q : Type} [Group Q] (pi : G →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (max t a) := by
  letI : Finite Q := Finite.of_surjective pi hpi
  let F := E.map pi
  letI : F.Normal := (inferInstance : E.Normal).map pi hpi
  let f : G ⧸ E →* Q ⧸ F :=
    QuotientGroup.map E F pi (Subgroup.le_comap_map pi E)
  have hf : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective E F pi
      ((QuotientGroup.mk'_surjective F).comp hpi) (Subgroup.le_comap_map pi E)
  have hcopF : Nat.Coprime p (Nat.card (Q ⧸ F)) :=
    hcop.of_dvd_right (Subgroup.card_dvd_of_surjective f hf)
  apply socleBound_of_kernel p F (hE.map pi) hcopF t a
  · intro H hH hHF
    letI := hH
    exact CoprimeCyclicQuotientSocleBounds.image_normalGen_le pi hpi E t hkernel H hHF
  · intro K hK
    letI := hK
    exact normalGen_image_bound f hf a hquotient K

theorem quotient (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    (hcop : Nat.Coprime p (Nat.card (G ⧸ E))) (t a : ℕ)
    (hkernel : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ t)
    (hquotient : ∀ K : Subgroup (G ⧸ E), K.Normal → MarkedC4.normalGen K ≤ a)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) (max t a) :=
  socle_of_surjective p E hE hcop t a hkernel hquotient
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CoprimeKernelQuotientSocles
end SymmetricSubgroupAsymptotics

end
