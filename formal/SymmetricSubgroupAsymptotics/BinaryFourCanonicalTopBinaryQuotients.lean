import SymmetricSubgroupAsymptotics.BinaryFourSymmetricKleinNormalCover
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricNaturalChart
import SymmetricSubgroupAsymptotics.NormalOrderTwo

/-! Actual top normal denominators in canonical A4 and S4. A normal binary
subgroup of the unquotiented top lies in literal Klein. A nonzero normal
denominator contains Klein; its binary quotient contribution has at most
one central binary coordinate (and vanishes in the A4 case). -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopBinaryQuotients
open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions SemidirectProduct

local instance : Fintype Klein :=
  Fintype.ofEquiv Local (Multiplicative.ofAdd : Local ≃ Klein)
local instance : Fintype Ternary :=
  Fintype.ofEquiv (ZMod 3) (Multiplicative.ofAdd : ZMod 3 ≃ Ternary)
local instance : Fintype Binary :=
  Fintype.ofEquiv (ZMod 2) (Multiplicative.ofAdd : ZMod 2 ≃ Binary)

local instance : DecidableEq Klein := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))
local instance : DecidableEq Ternary := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))
local instance : DecidableEq Binary := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))


private theorem binary_cube_eq_one {G : Type} [Group G]
    (H : Subgroup G) (hH : IsPGroup 2 H) (g : H) (hg : (g : G)^3 = 1) :
    (g : G) = 1 := by
  obtain ⟨n,hn⟩ := hH g
  have h2 : (g : G)^(2^n) = 1 := congrArg Subtype.val hn
  have ho : orderOf (g : G) = 1 := Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 3).pow_left n)
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hg)
  exact orderOf_eq_one_iff.mp ho

theorem a4_binary_normal_le_klein (H : Subgroup Complement) [H.Normal]
    (hH : IsPGroup 2 H) : H ≤ BinaryKleinTernaryNormalChain.kleinKernel := by
  intro g hg
  have detect : ∀ g : Complement,
      g ∉ BinaryKleinTernaryNormalChain.kleinKernel → g^3 = 1 ∧ g ≠ 1 := by
    have finite : ∀ (p : Klein) (z : Ternary), z ≠ 1 →
        ((⟨p,z⟩ : Complement)^3).left = 1 ∧
        ((⟨p,z⟩ : Complement)^3).right = 1 := by decide +kernel
    rintro ⟨p,z⟩ hz
    have hz' : z ≠ 1 := hz
    have h := finite p z hz'
    refine ⟨SemidirectProduct.ext h.1 h.2,?_⟩
    intro heq
    exact hz' (congrArg (fun a : Complement => a.right) heq)
  by_contra hnot
  have hd := detect g hnot
  exact hd.2 (binary_cube_eq_one H hH ⟨g,hg⟩ hd.1)

private def cubicWitness (g : SymmetricComplement) : Prop :=
  (g^3).left.left = 1 ∧ (g^3).left.right = 1 ∧ (g^3).right = 1 ∧
    ¬(g.left.left = 1 ∧ g.left.right = 1 ∧ g.right = 1)

private theorem cubicWitness_spec (g : SymmetricComplement) (h : cubicWitness g) :
    g^3 = 1 ∧ g ≠ 1 := by
  refine ⟨SemidirectProduct.ext (SemidirectProduct.ext h.1 h.2.1) h.2.2.1,?_⟩
  intro heq
  apply h.2.2.2
  exact ⟨congrArg (fun q : SymmetricComplement => q.left.left) heq,
    congrArg (fun q : SymmetricComplement => q.left.right) heq,
    congrArg (fun q : SymmetricComplement => q.right) heq⟩

theorem s4_binary_normal_le_klein (H : Subgroup SymmetricComplement) [H.Normal]
    (hH : IsPGroup 2 H) : H ≤ BinaryFourSymmetricKleinNormalCover.klein := by
  intro g hg
  have detect : ∀ g : SymmetricComplement,
      g ∉ BinaryFourSymmetricKleinNormalCover.klein →
      (g^3 = 1 ∧ g ≠ 1) ∨
      ∃ x : SymmetricComplement,
        (g*(x*g*x⁻¹))^3 = 1 ∧ g*(x*g*x⁻¹) ≠ 1 := by
    have finite : ∀ (p : Klein) (z : Ternary) (b : Binary),
        ¬(z = 1 ∧ b = 1) →
        cubicWitness (⟨⟨p,z⟩,b⟩ : SymmetricComplement) ∨
        ∃ (xp : Klein) (xz : Ternary) (xb : Binary),
          cubicWitness ((⟨⟨p,z⟩,b⟩ : SymmetricComplement) *
            ((⟨⟨xp,xz⟩,xb⟩ : SymmetricComplement) * ⟨⟨p,z⟩,b⟩ *
              (⟨⟨xp,xz⟩,xb⟩ : SymmetricComplement)⁻¹)) := by
      simp only [cubicWitness]
      decide +kernel
    rintro ⟨⟨p,z⟩,b⟩ hnot
    have hn : ¬(z = 1 ∧ b = 1) := fun h => hnot
      ((BinaryFourSymmetricKleinNormalCover.mem_klein _).mpr h)
    rcases finite p z b hn with h | ⟨xp,xz,xb,h⟩
    · exact Or.inl (cubicWitness_spec _ h)
    · exact Or.inr ⟨⟨⟨xp,xz⟩,xb⟩,cubicWitness_spec _ h⟩
  by_contra hnot
  rcases detect g hnot with hd | ⟨x,hcube,hne⟩
  · exact hd.2 (binary_cube_eq_one H hH ⟨g,hg⟩ hd.1)
  · have hm : g*(x*g*x⁻¹) ∈ H := H.mul_mem hg (Subgroup.Normal.conj_mem inferInstance g hg x)
    exact hne (binary_cube_eq_one H hH ⟨_,hm⟩ hcube)

private def a4KleinEquiv : BinaryKleinTernaryNormalChain.kleinKernel ≃ Klein where
  toFun g := g.1.left
  invFun p := ⟨inl p,rfl⟩
  left_inv g := Subtype.ext (SemidirectProduct.ext rfl (show g.1.right = 1 from g.2).symm)
  right_inv p := rfl

private def s4KleinEquiv : BinaryFourSymmetricKleinNormalCover.klein ≃ Klein where
  toFun g := g.1.left.left
  invFun p := ⟨inl (inl p),(BinaryFourSymmetricKleinNormalCover.mem_klein _).mpr ⟨rfl,rfl⟩⟩
  left_inv g := by
    apply Subtype.ext
    obtain ⟨ht,hb⟩ := (BinaryFourSymmetricKleinNormalCover.mem_klein g.1).mp g.2
    exact SemidirectProduct.ext (SemidirectProduct.ext rfl ht.symm) hb.symm
  right_inv p := rfl

private theorem klein_card : Nat.card Klein = 4 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Klein ≃ Local), Nat.card_eq_fintype_card]
  decide +kernel

private theorem a4_quotient_klein_card :
    Nat.card (Complement ⧸ BinaryKleinTernaryNormalChain.kleinKernel) = 3 := by
  have hk : Nat.card BinaryKleinTernaryNormalChain.kleinKernel = 4 :=
    (Nat.card_congr a4KleinEquiv).trans klein_card
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    BinaryKleinTernaryNormalChain.kleinKernel
  rw [BinaryFourCanonicalInducedChart.complement_card,hk] at h
  omega

private theorem s4_quotient_klein_card :
    Nat.card (SymmetricComplement ⧸ BinaryFourSymmetricKleinNormalCover.klein) = 6 := by
  have hk : Nat.card BinaryFourSymmetricKleinNormalCover.klein = 4 :=
    (Nat.card_congr s4KleinEquiv).trans klein_card
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    BinaryFourSymmetricKleinNormalCover.klein
  rw [BinaryFourCanonicalSymmetricInducedChart.symmetricComplement_card,hk] at h
  omega

private theorem quotient_card_dvd {G : Type} [Group G] [Finite G]
    (K N : Subgroup G) [K.Normal] [N.Normal] (hKN : K ≤ N) :
    Nat.card (G ⧸ N) ∣ Nat.card (G ⧸ K) := by
  let f : G ⧸ K →* G ⧸ N := QuotientGroup.map K N (MonoidHom.id G) hKN
  have hf : Function.Surjective f := QuotientGroup.map_surjective_of_surjective
    K N (MonoidHom.id G) (QuotientGroup.mk'_surjective N) hKN
  exact Subgroup.card_dvd_of_surjective f hf

theorem a4_nonzero_quotient_card_dvd (N : Subgroup Complement) [N.Normal]
    (hN : N ≠ ⊥) : Nat.card (Complement ⧸ N) ∣ 3 := by
  simpa only [a4_quotient_klein_card] using quotient_card_dvd
    BinaryKleinTernaryNormalChain.kleinKernel N
    (BinaryKleinTernaryNormalChain.kleinKernel_le_normal N inferInstance hN)

theorem s4_nonzero_quotient_card_dvd (N : Subgroup SymmetricComplement) [N.Normal]
    (hN : N ≠ ⊥) : Nat.card (SymmetricComplement ⧸ N) ∣ 6 := by
  simpa only [s4_quotient_klein_card] using quotient_card_dvd
    BinaryFourSymmetricKleinNormalCover.klein N
    (BinaryFourSymmetricKleinNormalCover.le_normal N inferInstance hN)

private theorem binary_card_le_two_of_dvd_six {H : Type} [Group H] [Finite H]
    (hH : IsPGroup 2 H) (hd : Nat.card H ∣ 6) : Nat.card H = 1 ∨ Nat.card H = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n,hn⟩ := hH.exists_card_eq
  have hle : 2^n ≤ 6 := hn ▸ Nat.le_of_dvd (by decide) hd
  have hnle : n ≤ 2 := by
    by_contra hnot
    have h8 : 8 ≤ 2^n := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 3 ≤ n)
    omega
  rw [hn] at hd
  have hn2 : n ≠ 2 := by
    intro h
    subst n
    norm_num at hd
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · exact Or.inl (by simpa only [pow_zero] using hn)
  · exact Or.inr (by simpa only [pow_one] using hn)

theorem s4_nonzero_binary_card (N : Subgroup SymmetricComplement) [N.Normal]
    (hN : N ≠ ⊥) (H : Subgroup (SymmetricComplement ⧸ N))
    (hH : IsPGroup 2 H) : Nat.card H = 1 ∨ Nat.card H = 2 :=
  binary_card_le_two_of_dvd_six hH
    (H.card_subgroup_dvd_card.trans (s4_nonzero_quotient_card_dvd N hN))

theorem s4_nonzero_binary_normal_central (N : Subgroup SymmetricComplement) [N.Normal]
    (hN : N ≠ ⊥) (H : Subgroup (SymmetricComplement ⧸ N)) [H.Normal]
    (hH : IsPGroup 2 H) : H ≤ Subgroup.center (SymmetricComplement ⧸ N) := by
  rcases s4_nonzero_binary_card N hN H hH with hc | hc
  · rw [H.eq_bot_of_card_eq hc]
    exact bot_le
  · exact NormalOrderTwo.le_center H hc

theorem a4_nonzero_binary_eq_bot (N : Subgroup Complement) [N.Normal]
    (hN : N ≠ ⊥) (H : Subgroup (Complement ⧸ N))
    (hH : IsPGroup 2 H) : H = ⊥ := by
  have hd : Nat.card H ∣ 3 := H.card_subgroup_dvd_card.trans (a4_nonzero_quotient_card_dvd N hN)
  rcases binary_card_le_two_of_dvd_six hH (hd.trans (by decide : 3 ∣ 6)) with hc | hc
  · exact H.eq_bot_of_card_eq hc
  · rw [hc] at hd
    norm_num at hd

end SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopBinaryQuotients
end
