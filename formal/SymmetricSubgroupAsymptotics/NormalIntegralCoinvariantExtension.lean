import SymmetricSubgroupAsymptotics.PrimeRelativeHeadSurjectiveKernel
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import Mathlib.Tactic.Ring

/-! Full integral coinvariant orders across an actual elementary kernel.
Only the exponent-p kernel intersection is paid by its relative head;
all higher cyclic factors in the original normal and top image remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The full order N/[N,G], including higher cyclic factors. -/
def normalIntegralCoinvariantOrder {G : Type} [Group G] (N : Subgroup G) : ℕ :=
  (⁅N,(⊤ : Subgroup G)⁆).relIndex N

private theorem relativeIndex_mul_subgroup_card
    {G : Type} [Group G] [Finite G] (A B : Subgroup G) (hBA : B≤A) :
    B.relIndex A*Nat.card B=Nat.card A := by
  have hc := (B.subgroupOf A).card_mul_index
  have he : Nat.card (B.subgroupOf A)=Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  rw [he] at hc
  exact (Nat.mul_comm _ _).trans hc

/-- This is a full-order inequality, not an inequality of prime heads. -/
theorem normalIntegralCoinvariantOrder_le_elementary_kernel
    {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (f : G →* H) (hf : Function.Surjective f)
    (hpow : ∀ k : f.ker,(k : G)^p=1)
    (N : Subgroup G) [N.Normal] :
    normalIntegralCoinvariantOrder N≤
      p^MarkedC4.normalGen (N ⊓ f.ker)*normalIntegralCoinvariantOrder (N.map f) := by
  let A := N ⊓ f.ker
  let C := ⁅N,(⊤ : Subgroup G)⁆
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hCA : primeRelativeRadical p A≤C ⊓ f.ker := by
    rw [primeRelativeRadical_eq_powerCommutator]
    apply sup_le
    · apply (Subgroup.closure_le _).mpr
      rintro x ⟨a,rfl⟩
      change (a : G)^p∈C ⊓ f.ker
      rw [hpow ⟨a.val,a.property.2⟩]
      exact Subgroup.one_mem _
    · exact le_inf
        (Subgroup.commutator_mono (show A≤N from inf_le_left) le_rfl)
        ((Subgroup.commutator_le_left A ⊤).trans (show A≤f.ker from inf_le_right))
  have hA : Nat.card A≤p^MarkedC4.normalGen A*Nat.card (C ⊓ f.ker : Subgroup G) := by
    have he := primeRelativeRadical_card_factorization p A
    rw [←pGroup_normalGen_eq_primeRelativeHead p hG A] at he
    exact he.le.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hCA))
  have hCmap : C.map f=⁅N.map f,(⊤ : Subgroup H)⁆ := by
    dsimp only [C]
    rw [Subgroup.map_commutator,Subgroup.map_top_of_surjective f hf]
  have hNcard := subgroup_card_eq_map_mul_kernel_intersection f N
  have hCcard := subgroup_card_eq_map_mul_kernel_intersection f C
  have hsource : normalIntegralCoinvariantOrder N*Nat.card C=Nat.card N :=
    relativeIndex_mul_subgroup_card N C (Subgroup.commutator_le_left N ⊤)
  have htop : normalIntegralCoinvariantOrder (N.map f)*Nat.card (C.map f)=Nat.card (N.map f) := by
    rw [hCmap]
    exact relativeIndex_mul_subgroup_card (N.map f) _
      (Subgroup.commutator_le_left (N.map f) ⊤)
  have hb : normalIntegralCoinvariantOrder N*
      (Nat.card (C.map f)*Nat.card (C ⊓ f.ker : Subgroup G))≤
      (p^MarkedC4.normalGen A*normalIntegralCoinvariantOrder (N.map f))*
        (Nat.card (C.map f)*Nat.card (C ⊓ f.ker : Subgroup G)) := by
    calc
      _ = normalIntegralCoinvariantOrder N*Nat.card C := by rw [hCcard]
      _ = Nat.card N := hsource
      _ = Nat.card (N.map f)*Nat.card A := hNcard
      _ ≤ Nat.card (N.map f)*(p^MarkedC4.normalGen A*Nat.card (C ⊓ f.ker : Subgroup G)) :=
        Nat.mul_le_mul_left _ hA
      _ = _ := by rw [←htop];ring
  exact Nat.le_of_mul_le_mul_right hb (Nat.mul_pos Nat.card_pos Nat.card_pos)

end SymmetricSubgroupAsymptotics
