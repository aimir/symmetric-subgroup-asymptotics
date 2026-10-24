import SymmetricSubgroupAsymptotics.SmallAffineSoluble8Row2Order
import SymmetricSubgroupAsymptotics.PrimeSelfCentralizingSubnormal
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.NormNum.Prime
import Lean.Elab.Tactic.Omega

/-! The actual order-twenty-one complement has a literal normal,
self-centralizing subgroup of order seven. Only its already checked
twenty-one element word menu is inspected, not its subgroup lattice. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SmallAffineTwentyOneSelfCentralizingSeven
open SmallAffineSoluble8Row2Order

def singer : R := ⟨g0,Subgroup.subset_closure ⟨0,rfl⟩⟩

def seven : Subgroup R := Subgroup.zpowers singer

theorem singer_order : orderOf singer = 7 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro he
    have hh : g0 = 1 := congrArg (fun z : R => z.val) he
    exact (by decide +kernel : g0 ≠ 1) hh

theorem seven_card : Nat.card seven = 7 := by
  rw [seven,Nat.card_zpowers,singer_order]

theorem seven_normal : seven.Normal := by
  have hindex : seven.index = 3 := by
    have h := seven.card_mul_index
    rw [seven_card,card] at h
    omega
  apply seven.normal_of_index_eq_minFac_card
  rw [hindex,card]
  norm_num

private theorem centralizing_rows :
    ∀ i : Fin 21, elements i * g0 = g0 * elements i →
      ∃ j : Fin 7, elements i = g0 ^ j.val := by
  decide +kernel

theorem centralizer_le_seven : Subgroup.centralizer (seven : Set R) ≤ seven := by
  intro z hz
  have hs : singer ∈ seven := Subgroup.mem_zpowers singer
  have hc : singer * z = z * singer := hz singer hs
  have hc' : g0 * z.val = z.val * g0 := congrArg (fun w : R => w.val) hc
  obtain ⟨i,hi⟩ := (certificate.mem_closure_iff z.val).mp z.property
  change elements i = z.val at hi
  have hiCommute : elements i * g0 = g0 * elements i := by
    rw [hi]
    exact hc'.symm
  obtain ⟨j,hj⟩ := centralizing_rows i hiCommute
  have hzpow : z = singer ^ j.val := Subtype.ext (hi.symm.trans hj)
  rw [hzpow]
  exact seven.pow_mem hs j.val

theorem seven_le_of_nontrivial_subnormal
    (N : Subgroup R) (hN : N.IsSubnormal) (hne : N ≠ ⊥) : seven ≤ N := by
  letI : seven.Normal := seven_normal
  exact PrimeSelfCentralizingSubnormal.le_of_nontrivial_subnormal seven
    (by rw [seven_card]; decide) centralizer_le_seven N hN hne

end SymmetricSubgroupAsymptotics.SmallAffineTwentyOneSelfCentralizingSeven
