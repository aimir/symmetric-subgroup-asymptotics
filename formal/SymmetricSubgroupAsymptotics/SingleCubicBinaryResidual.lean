import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index

/-! In an actual finite group with a SINGLE cubic factor in its order,
the normal closure of an actual subgroup of order three is exactly the
retained separator for binary quotients. No splitting is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SingleCubicBinaryResidual
variable {G : Type} [Group G]

def retained (P : Subgroup G) : Subgroup G := Subgroup.normalClosure (P : Set G)
instance retained_normal (P : Subgroup G) : (retained P).Normal := by
  change (Subgroup.normalClosure (P : Set G)).Normal
  infer_instance

theorem binary_quotient (P : Subgroup G) (hP : Nat.card P=3)
    (k : ℕ) (hG : Nat.card G=3*2^k) : IsPGroup 2 (G ⧸ retained P) := by
  let D := retained P
  have hPD : P≤D := Subgroup.subset_normalClosure
  have hdiv : 3∣Nat.card D := by
    rw [← hP]
    exact Subgroup.card_dvd_of_le hPD
  obtain ⟨m,hm⟩ := hdiv
  have hp := D.card_mul_index
  rw [Subgroup.index_eq_card,hm,hG] at hp
  have hc : m*Nat.card (G ⧸ D)=2^k := Nat.eq_of_mul_eq_mul_left
    (by decide : 0<3) (by simpa only [Nat.mul_assoc] using hp)
  have hqd : Nat.card (G ⧸ D)∣2^k := ⟨m,by simpa only [Nat.mul_comm] using hc.symm⟩
  obtain ⟨n,hn⟩ := hqd
  intro x
  refine ⟨k,?_⟩
  rw [hn,pow_mul,pow_card_eq_one',one_pow]

theorem retained_le_of_binary_quotient (P : Subgroup G) (hP : Nat.card P=3)
    (N : Subgroup G) [N.Normal] (hbinary : IsPGroup 2 (G ⧸ N)) : retained P≤N := by
  apply Subgroup.normalClosure_le_normal
  intro g hg
  let p : P := ⟨g,hg⟩
  have hp : g^3=1 := by
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := p))
    simpa only [hP,Subgroup.coe_pow,Subgroup.coe_one] using hh
  apply (QuotientGroup.eq_one_iff (N := N) g).mp
  apply (hbinary.powEquiv (by decide : Nat.Coprime 2 3)).injective
  have hc := congrArg (QuotientGroup.mk' N) hp
  simpa only [IsPGroup.powEquiv_apply,map_pow,map_one,one_pow] using hc

theorem binary_iff_retained_le (P : Subgroup G) (hP : Nat.card P=3)
    (k : ℕ) (hG : Nat.card G=3*2^k) (N : Subgroup G) [N.Normal] :
    IsPGroup 2 (G ⧸ N) ↔ retained P≤N := by
  constructor
  · exact retained_le_of_binary_quotient P hP N
  · intro hDN
    let f : (G ⧸ retained P) →* (G ⧸ N) :=
      QuotientGroup.lift (retained P) (QuotientGroup.mk' N) (by
        intro g hg
        exact (QuotientGroup.eq_one_iff (N := N) g).mpr (hDN hg))
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N y
      exact ⟨QuotientGroup.mk' (retained P) g,rfl⟩
    exact (binary_quotient P hP k hG).of_surjective f hf

end SymmetricSubgroupAsymptotics.SingleCubicBinaryResidual
