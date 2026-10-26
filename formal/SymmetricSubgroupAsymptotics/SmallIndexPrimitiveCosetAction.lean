import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finite.Card
import Lean.Elab.Tactic.Omega

/-! Every proper subgroup with index below twice the actual minimum
proper-index floor is maximal. Consequently its original coset action
is primitive, without any primitive hypothesis on another action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallIndexPrimitiveCosetAction

variable {G : Type*} [Group G] [Finite G]

/-- Index multiplicativity rules out every genuine intermediate subgroup. -/
theorem isCoatom_of_index_lt_twice
    (b : ℕ) (hlower : ∀ L : Subgroup G, L ≠ ⊤ → b ≤ L.index)
    (K : Subgroup G) (hK : K ≠ ⊤) (hsmall : K.index < 2*b) :
    IsCoatom K := by
  refine ⟨hK,?_⟩
  intro L hKL
  by_contra hL
  have hmul : K.relIndex L * L.index = K.index :=
    Subgroup.relIndex_mul_index hKL.le
  have hzero : K.relIndex L ≠ 0 := by
    intro he
    rw [he,zero_mul] at hmul
    exact K.index_ne_zero_of_finite hmul.symm
  have hone : K.relIndex L ≠ 1 := by
    intro he
    exact hKL.not_ge ((Subgroup.relIndex_eq_one (H:=K) (K:=L)).mp he)
  have htwo : 2 ≤ K.relIndex L := by omega
  have hbound : 2*b ≤ K.index := by
    calc
      _ ≤ K.relIndex L * L.index := Nat.mul_le_mul htwo (hlower L hL)
      _ = K.index := hmul
  omega

/-- This is the SAME original left-coset action attached to K. -/
theorem coset_isPreprimitive_of_index_lt_twice
    (b : ℕ) (hlower : ∀ L : Subgroup G, L ≠ ⊤ → b ≤ L.index)
    (K : Subgroup G) (hK : K ≠ ⊤) (hsmall : K.index < 2*b) :
    MulAction.IsPreprimitive G (G ⧸ K) := by
  letI : Nontrivial (G ⧸ K) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [←K.index_eq_card]
    exact K.one_lt_index_of_ne_top hK)
  apply (MulAction.isCoatom_stabilizer_iff_preprimitive G ((1:G) : G ⧸ K)).mp
  rw [MulAction.stabilizer_quotient]
  exact isCoatom_of_index_lt_twice b hlower K hK hsmall

end SymmetricSubgroupAsymptotics.SmallIndexPrimitiveCosetAction
