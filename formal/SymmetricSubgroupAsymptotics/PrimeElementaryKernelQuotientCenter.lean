import SymmetricSubgroupAsymptotics.PrimeRelativeHeadSurjectiveKernel
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality

/-! The central part of an actual image of an elementary normal kernel
is paid by one original normal preimage inside that kernel. A uniform
original normal-generator bound therefore bounds this central image's
ORDER, since this image really has exponent p. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]

/-- Centrality and actual exponent p, rather than a general rank-to-order
substitution, justify this exact order identity. -/
theorem pGroup_central_exponent_subgroup_card_eq_pow_normalGen
    {G : Type} [Group G] [Finite G] (hG : IsPGroup p G)
    (C : Subgroup G) [C.Normal] (hC : C≤Subgroup.center G)
    (hpow : ∀ c : C, (c : G)^p=1) :
    Nat.card C=p^MarkedC4.normalGen C := by
  have hR : primeRelativeRadical p C=⊥ := by
    rw [primeRelativeRadical_eq_powerCommutator,primeRelativePowerCommutator]
    apply le_antisymm ?_ bot_le
    apply sup_le
    · apply (Subgroup.closure_le (⊥ : Subgroup G)).mpr
      rintro x ⟨c,rfl⟩
      change (c : G)^p∈(⊥ : Subgroup G)
      rw [hpow c]
      exact Subgroup.one_mem _
    · apply Subgroup.commutator_le.mpr
      intro c hc g _
      change ⁅c,g⁆=1
      have he : g*c=c*g := Subgroup.mem_center_iff.mp (hC hc) g
      rw [commutatorElement_def,←he]
      simp only [mul_assoc,mul_inv_cancel,mul_one]
  have hc := primeRelativeRadical_card_factorization p C
  rw [←pGroup_normalGen_eq_primeRelativeHead p hG C,hR,Subgroup.card_bot,mul_one] at hc
  exact hc

/-- All subgroups are actual original ambient normals, not independent
coordinate projections of the image. -/
theorem pGroup_central_kernel_image_card_le_of_normalHead_bound
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (hG : IsPGroup p G) (q : G →* Q) (hq : Function.Surjective q)
    (K : Subgroup G) [K.Normal] (hpow : ∀ k : K, (k : G)^p=1)
    (d : ℕ) (hbound : ∀ (A : Subgroup G) [A.Normal], A≤K → MarkedC4.normalGen A≤d) :
    Nat.card (K.map q ⊓ Subgroup.center Q : Subgroup Q)≤p^d := by
  letI : (K.map q).Normal := Subgroup.Normal.map inferInstance q hq
  let C : Subgroup Q := K.map q ⊓ Subgroup.center Q
  let A : Subgroup G := K ⊓ C.comap q
  have hmap : A.map q=C := by
    apply le_antisymm
    · rintro x ⟨a,ha,rfl⟩
      exact ha.2
    · intro x hx
      obtain ⟨a,ha,he⟩ := hx.1
      exact ⟨a,⟨ha,by change q a∈C;rw [he];exact hx⟩,he⟩
  have hCpow (c : C) : (c : Q)^p=1 := by
    obtain ⟨k,hk,he⟩ := c.property.1
    rw [←he,←map_pow,hpow ⟨k,hk⟩,map_one]
  have hc : Nat.card C=p^MarkedC4.normalGen C :=
    pGroup_central_exponent_subgroup_card_eq_pow_normalGen p (hG.of_surjective q hq)
      C inf_le_right hCpow
  have hm := MarkedC4.normalGen_map_le q hq A
  rw [hmap] at hm
  rw [hc]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (hm.trans (hbound A inf_le_left))

/-- The full centre is charged by its actual kernel part and its image
in the centre of the actual target. -/
theorem center_card_le_kernel_part_mul_target_center
    {Q H : Type} [Group Q] [Finite Q] [Group H] [Finite H]
    (f : Q →* H) (hf : Function.Surjective f) :
    Nat.card (Subgroup.center Q) ≤
      Nat.card (f.ker ⊓ Subgroup.center Q : Subgroup Q)*Nat.card (Subgroup.center H) := by
  have hm : (Subgroup.center Q).map f≤Subgroup.center H := by
    rintro x ⟨c,hc,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro h
    obtain ⟨g,rfl⟩ := hf h
    rw [←map_mul,←map_mul,Subgroup.mem_center_iff.mp hc g]
  have hc := subgroup_card_eq_map_mul_kernel_intersection f (Subgroup.center Q)
  rw [inf_comm] at hc
  rw [hc]
  calc
    _ ≤ Nat.card (Subgroup.center H)*
        Nat.card (f.ker ⊓ Subgroup.center Q : Subgroup Q) :=
      Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hm)
    _ = _ := Nat.mul_comm _ _

/-- RDT5.6(ii)'s centre factor, for the actual two-step image extension.
The only capacity is a bound on original normal subgroups inside K. -/
theorem pGroup_quotient_center_card_le_of_elementary_kernel_normalHead_bound
    {G Q H : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    [Group H] [Finite H]
    (hG : IsPGroup p G) (q : G →* Q) (hq : Function.Surjective q)
    (K : Subgroup G) [K.Normal] (hpow : ∀ k : K, (k : G)^p=1)
    (d : ℕ) (hbound : ∀ (A : Subgroup G) [A.Normal], A≤K → MarkedC4.normalGen A≤d)
    (f : Q →* H) (hf : Function.Surjective f) (hker : f.ker=K.map q) :
    Nat.card (Subgroup.center Q)≤p^d*Nat.card (Subgroup.center H) := by
  have hc := center_card_le_kernel_part_mul_target_center f hf
  rw [hker] at hc
  exact hc.trans (Nat.mul_le_mul_right _
    (pGroup_central_kernel_image_card_le_of_normalHead_bound p hG q hq K hpow d hbound))

end SymmetricSubgroupAsymptotics
