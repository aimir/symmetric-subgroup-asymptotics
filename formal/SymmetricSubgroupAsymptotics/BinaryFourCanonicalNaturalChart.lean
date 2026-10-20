import SymmetricSubgroupAsymptotics.BinaryFourCanonicalInducedChart
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Exact natural A4 point and stabilizer charts for the canonical
induced-plane model. Only twelve affine block elements are checked. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryFourCanonicalInducedChart

open BinaryFourBlockAugmentation

theorem blocks_injective : Function.Injective blocks := by
  intro r s hrs
  rcases r with ⟨p, z⟩
  rcases s with ⟨q, w⟩
  have detect : ∀ (p q : Klein) (z w : Ternary),
      blocks ⟨p, z⟩ = blocks ⟨q, w⟩ → p = q ∧ z = w := by decide +kernel
  obtain ⟨hp, hz⟩ := detect p q z w hrs
  exact SemidirectProduct.ext hp hz

theorem complement_card : Nat.card Complement = 12 := by
  have hk : Nat.card Klein = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Klein ≃ Local), Nat.card_eq_fintype_card]
    decide +kernel
  have ht : Nat.card Ternary = 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Ternary ≃ ZMod 3), Nat.card_zmod]
  rw [Nat.card_congr (SemidirectProduct.equivProd : Complement ≃ Klein × Ternary),
    Nat.card_prod, hk, ht]

theorem blocks_range : blocks.range = alternatingGroup (Fin 4) := by
  have hle : blocks.range ≤ alternatingGroup (Fin 4) := by
    rintro _ ⟨r, rfl⟩
    rcases r with ⟨p, z⟩
    change Equiv.Perm.sign (blocks ⟨p, z⟩) = 1
    revert p z
    decide +kernel
  apply Subgroup.eq_of_le_of_card_ge hle
  have hc : Nat.card blocks.range = 12 :=
    (Nat.card_congr (MonoidHom.ofInjective blocks_injective).toEquiv).symm.trans complement_card
  rw [hc, nat_card_alternatingGroup]
  norm_num

def naturalGroupEquiv : Complement ≃* alternatingGroup (Fin 4) :=
  (MonoidHom.ofInjective blocks_injective).trans (MulEquiv.subgroupCongr blocks_range)

/-- Under this exact group chart the four physical points stay fixed. -/
theorem naturalGroupEquiv_apply (r : Complement) (i : Fin 4) :
    (naturalGroupEquiv r).1 i = r • i := by rfl

def stabilizerTernary : stabilizer →* Ternary where
  toFun h := h.1.right
  map_one' := rfl
  map_mul' _ _ := rfl

theorem stabilizerTernary_injective : Function.Injective stabilizerTernary := by
  have fixedZero : ∀ (p : Klein) (z : Ternary),
      blocks ⟨p, z⟩ 0 = 0 → p = 1 := by decide +kernel
  intro h k heq
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact (fixedZero h.1.left h.1.right h.2).trans
      (fixedZero k.1.left k.1.right k.2).symm
  · exact heq

theorem stabilizerTernary_surjective : Function.Surjective stabilizerTernary := by
  intro z
  refine ⟨⟨SemidirectProduct.inr z, ?_⟩, rfl⟩
  change blocks (SemidirectProduct.inr z) 0 = 0
  revert z
  decide +kernel

def stabilizerTernaryEquiv : stabilizer ≃* Ternary :=
  MulEquiv.ofBijective stabilizerTernary
    ⟨stabilizerTernary_injective, stabilizerTernary_surjective⟩

end SymmetricSubgroupAsymptotics.BinaryFourCanonicalInducedChart

end
