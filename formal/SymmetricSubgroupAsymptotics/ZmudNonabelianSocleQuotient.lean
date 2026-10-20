import SymmetricSubgroupAsymptotics.ZmudNonabelianSocleDetection
import SymmetricSubgroupAsymptotics.MarkedC4SocleSurjectiveImage
import SymmetricSubgroupAsymptotics.AbelianNormalSocleCentralization

/-! Applying the nonabelian detector to the literal quotient by the
abelian socle makes it trivial on every abelian minimal normal subgroup,
while every nonabelian minimal normal embeds and remains minimal normal
and nonabelian in that quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.ZmudNonabelianSocleQuotient

open ZmudFixedSpaceConstituents ZmudNonabelianSocleDetection

variable {G : Type} [Group G] [Finite G]

private def abelianPart (G : Type) [Group G] [Finite G] : Subgroup G :=
  minimalNormalSoclePart G (fun N => IsMulCommutative N)

private instance abelianPart_normal : (abelianPart G).Normal := by
  dsimp only [abelianPart]
  infer_instance

private theorem abelianPart_commutative : IsMulCommutative (abelianPart G) := by
  let A := abelianPart G
  have hAS : A ≤ finiteGroupSocle G := minimalNormalSoclePart_le_finiteGroupSocle G _
  apply Subgroup.le_centralizer_iff_isMulCommutative.mp
  apply minimalNormalSoclePart_le_of
  intro N hN hcomm
  letI : N.Normal := hN.1
  letI : IsMulCommutative N := hcomm
  have hc := finiteGroupSocle_le_centralizer_of_abelian_normal N
  intro n hn
  apply Subgroup.mem_centralizer_iff.mpr
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hc (hAS ha)) n hn).symm

omit [Finite G] in
private theorem quotient_injective (M A : Subgroup G) [A.Normal]
    (hdis : M ⊓ A = ⊥) :
    Function.Injective ((QuotientGroup.mk' A).comp M.subtype) := by
  intro x y hxy
  apply Subtype.ext
  apply mul_inv_eq_one.mp
  have hxA : x.1 * y.1⁻¹ ∈ A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' A (x.1 * y.1⁻¹) = 1
    rw [map_mul, map_inv]
    exact mul_inv_eq_one.mpr hxy
  have hx : x.1 * y.1⁻¹ ∈ M ⊓ A :=
    ⟨M.mul_mem x.2 (M.inv_mem y.2), hxA⟩
  rw [hdis] at hx
  exact Subgroup.mem_bot.mp hx

/-- The nonabelian detector, with literal triviality on every abelian
minimal normal subgroup of the original group. -/
theorem exists_envelope :
    ∃ F : Envelope G,
      (∀ (N : Subgroup G), IsMinimalNormalSubgroup N → IsMulCommutative N →
        ∀ (n : N) (v : F.Space), F.action n.1 v = v) ∧
      ∀ (N : Subgroup G), IsMinimalNormalSubgroup N → ¬ IsMulCommutative N →
        ∀ v : F.Space, (∀ n : N, F.action n.1 v = v) → v = 0 := by
  let A := abelianPart G
  letI : IsMulCommutative A := abelianPart_commutative
  let q := QuotientGroup.mk' A
  obtain ⟨r, hr⟩ := ZmudNonabelianSocleDetection.exists_irreducible (G := G ⧸ A)
  let F := inflate q (irreducibleEnvelope r)
  refine ⟨F, ?_, ?_⟩
  · intro N hN hcomm n v
    have hNA : N ≤ A := minimalNormal_le_minimalNormalSoclePart _ N hN hcomm
    change r.action (q n.1) v = v
    have hnq : q n.1 = 1 :=
      (QuotientGroup.eq_one_iff (N := A) (n.1 : G)).mpr (hNA n.2)
    rw [hnq, map_one, Module.End.one_apply]
  · intro N hN hnoncomm v hv
    letI : N.Normal := hN.1
    have hnot : ¬ N ≤ A := by
      intro hNA
      apply hnoncomm
      apply IsMulCommutative.of_comm
      intro x y
      apply Subtype.ext
      exact congrArg (fun z : A => (z : G))
        ((inferInstance : IsMulCommutative A).is_comm.comm
          (⟨x.1, hNA x.2⟩ : A) (⟨y.1, hNA y.2⟩ : A))
    have hdis : N ⊓ A = ⊥ := by
      by_contra hne
      have he := hN.2.2 (N ⊓ A) inferInstance hne inf_le_left
      exact hnot (by rw [← he]; exact inf_le_right)
    have hinj : Function.Injective (q.subgroupMap N) := by
      intro x y hxy
      exact quotient_injective N A hdis (congrArg Subtype.val hxy)
    have hmapne : N.map q ≠ ⊥ := by
      intro hb
      apply hnot
      have hle := (Subgroup.map_eq_bot_iff (H := N)).mp hb
      simpa only [q, QuotientGroup.ker_mk'] using hle
    have hmapmin := MarkedC4.SocleSurjectiveImage.minimalNormal_map
      q (QuotientGroup.mk'_surjective A) N hN hmapne
    have hmapnoncomm : ¬ IsMulCommutative (N.map q) := by
      intro hc
      apply hnoncomm
      apply IsMulCommutative.of_comm
      intro x y
      apply hinj
      rw [map_mul, map_mul]
      exact hc.is_comm.comm _ _
    apply hr (N.map q) hmapmin hmapnoncomm
    intro n
    obtain ⟨x, hx, he⟩ := n.2
    have hfix := hv ⟨x, hx⟩
    change r.action (q x) v = v at hfix
    simpa only [he] using hfix

end SymmetricSubgroupAsymptotics.ZmudNonabelianSocleQuotient
