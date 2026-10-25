import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Tactic.Group
import Lean.Elab.Tactic.Omega

/-! An actual central-modulo-normal involution doubles the index of a
preserving join when it is missing. The subgroup and its invariant sets
are retained literally; no complement or quotient splitting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise commutatorElement
namespace SymmetricSubgroupAsymptotics.CentralModuloNormalInvolutionJoin
variable {G : Type*} [Group G]

/-- Containment of the literal commutators suffices for normalization. -/
theorem mem_normalizer_of_commutators (N L : Subgroup G) (hNL : N≤L)
    (t : G) (hc : ∀g : G, ⁅t,g⁆∈N) : t∈Subgroup.normalizer (L : Set G) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  have hh : ⁅t,g⁆∈L := hNL (hc g)
  have he : ⁅t,g⁆*g=t*g*t⁻¹ := by rw [commutatorElement_def]; group
  rw [←he]
  exact (L.mul_mem_cancel_left hh).symm

/-- The actual cyclic involution enlarges the same subgroup by exactly two. -/
theorem index_double_of_normalizes [Finite G] (L : Subgroup G) (t : G)
    (ht : t^2=1) (htL : t∉L) (hnorm : t∈Subgroup.normalizer (L : Set G)) :
    (L⊔Subgroup.zpowers t).index*2=L.index := by
  let Z := Subgroup.zpowers t
  have ht1 : t≠1 := by intro h; exact htL (h ▸ L.one_mem)
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have ho : orderOf t=2 := orderOf_eq_prime ht ht1
  have hcZ : Nat.card Z=2 := (Nat.card_zpowers t).trans ho
  let U := L.subgroupOf Z
  have hUproper : U≠⊤ := by
    intro h
    have hmem : (⟨t,Subgroup.mem_zpowers t⟩ : Z)∈U := by rw [h]; trivial
    exact htL hmem
  have hle : Nat.card U≤Nat.card Z :=
    Nat.card_le_card_of_injective U.subtype Subtype.val_injective
  have hlt : Nat.card U<Nat.card Z := by
    by_contra h
    have he : Nat.card U=Nat.card Z := by omega
    apply hUproper
    exact Subgroup.eq_of_le_of_card_ge le_top
      (by simpa only [Subgroup.card_top] using he.ge)
  have hcU : Nat.card U=1 := by have hp := Nat.card_pos (α := U); omega
  have hi : U.index=2 := by
    have he := U.index_mul_card
    rw [hcU,hcZ,mul_one] at he
    exact he
  have hZ : Z≤Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr hnorm
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hZ
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hZ
  have he : U.index=(L.subgroupOf (Z⊔L)).index :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient Z L hZ).toEquiv
  have hrel : L.relIndex (L⊔Z)=2 := by
    change (L.subgroupOf (L⊔Z)).index=2
    rw [sup_comm]
    exact he.symm.trans hi
  have hfactor := Subgroup.relIndex_mul_index (show L≤L⊔Z from le_sup_left)
  rw [hrel,mul_comm] at hfactor
  exact hfactor

theorem index_double_of_commutators [Finite G]
    (N L : Subgroup G) (hNL : N≤L) (t : G)
    (ht : t^2=1) (htL : t∉L) (hc : ∀g : G, ⁅t,g⁆∈N) :
    (L⊔Subgroup.zpowers t).index*2=L.index :=
  index_double_of_normalizes L t ht htL (mem_normalizer_of_commutators N L hNL t hc)

/-- Setwise invariance is preserved on the same enlarged join. -/
theorem invariant_join {X : Type*} [MulAction G X]
    (L : Subgroup G) (t : G) (W : Set X)
    (hL : ∀g∈L,g•W=W) (ht : t•W=W) :
    ∀g∈L⊔Subgroup.zpowers t,g•W=W := by
  have hLS : L≤MulAction.stabilizer G W := by
    intro g hg
    exact hL g hg
  have htS : Subgroup.zpowers t≤MulAction.stabilizer G W :=
    Subgroup.zpowers_le.mpr ht
  exact sup_le hLS htS

end SymmetricSubgroupAsymptotics.CentralModuloNormalInvolutionJoin
