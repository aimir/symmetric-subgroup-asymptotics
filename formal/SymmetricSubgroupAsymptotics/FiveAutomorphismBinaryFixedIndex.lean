import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Every order-five automorphism of a finite two-group moves at least
fifteen sixteenths of that group. The group need not be abelian and its
Frattini quotient is not assumed faithful. Orbit congruence and the actual
fixed-subgroup index supply the whole bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiveAutomorphismBinaryFixedIndex

variable {G : Type*} [Group G]

def fixedSubgroup (a : MulAut G) : Subgroup G where
  carrier := {x | a x=x}
  one_mem' := a.map_one
  mul_mem' hx hy := by
    change a _ = _ at hx hy ⊢
    simp only [map_mul,hx,hy]
  inv_mem' hx := by
    change a _ = _ at hx ⊢
    simp only [map_inv,hx]

def fixedPointsEquiv (a : MulAut G) :
    MulAction.fixedPoints (Subgroup.zpowers a) G ≃ fixedSubgroup a where
  toFun x := ⟨x.val,x.property ⟨a,Subgroup.mem_zpowers a⟩⟩
  invFun x := ⟨x.val,by
    intro s
    obtain ⟨z,hz⟩ := Subgroup.mem_zpowers_iff.mp s.property
    change s.val x.val=x.val
    rw [← hz]
    have hx : x.val ∈ MulAction.fixedBy G a := x.property
    exact MulAction.mem_fixedBy_zpow hx z⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sixteen_le_index [Finite G] (hG : IsPGroup 2 G)
    (a : MulAut G) (ha : orderOf a=5) : 16 ≤ (fixedSubgroup a).index := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := fixedSubgroup a
  have hA : Nat.card (Subgroup.zpowers a)=5 := by rw [Nat.card_zpowers,ha]
  have hp : IsPGroup 5 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hA)
  have hmod := hp.card_modEq_card_fixedPoints G
  rw [Nat.card_congr (fixedPointsEquiv a)] at hmod
  change Nat.card G ≡ Nat.card F [MOD 5] at hmod
  obtain ⟨s,hs⟩ := (hG.to_subgroup F).exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card F) := by
    rw [hs]
    exact (show Nat.Coprime 5 2 from by decide).pow_right s
  have hi : F.index ≡ 1 [MOD 5] :=
    Nat.ModEq.cancel_left_of_coprime hcop (by
      simpa only [F.card_mul_index,mul_one] using hmod)
  have hne : a ≠ 1 := by
    intro he
    rw [he,orderOf_one] at ha
    norm_num at ha
  have hF : F ≠ ⊤ := by
    intro ht
    apply hne
    apply MulEquiv.ext
    intro x
    have hx : x ∈ F := ht ▸ Subgroup.mem_top x
    exact hx
  have hgt : 1 < F.index := F.one_lt_index_of_ne_top hF
  obtain ⟨e,he⟩ := hG.index F
  change 16 ≤ F.index
  rw [he]
  by_contra hbound
  have he4 : e < 4 := by
    by_contra h
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ e)
    norm_num only [show (2:ℕ)^4=16 from rfl] at hpow
    omega
  interval_cases e
  · norm_num [he] at hgt
  · norm_num [he,Nat.ModEq] at hi
  · norm_num [he,Nat.ModEq] at hi
  · norm_num [he,Nat.ModEq] at hi

theorem sixteen_mul_card_fixed_le [Finite G] (hG : IsPGroup 2 G)
    (a : MulAut G) (ha : orderOf a=5) :
    16*Nat.card (fixedSubgroup a) ≤ Nat.card G := by
  have h := Nat.mul_le_mul_left (Nat.card (fixedSubgroup a)) (sixteen_le_index hG a ha)
  simpa only [(fixedSubgroup a).card_mul_index,Nat.mul_comm] using h

end SymmetricSubgroupAsymptotics.FiveAutomorphismBinaryFixedIndex
