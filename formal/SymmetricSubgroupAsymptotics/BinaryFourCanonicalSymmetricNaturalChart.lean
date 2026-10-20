import SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricInducedChart
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalNaturalChart

/-! Natural S4 and its actual six-element point stabilizer, in the
retained symmetric-complement chart. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricInducedChart

open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions

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

theorem blocks_injective : Function.Injective blocks := by
  intro r s hrs
  rcases r with ⟨⟨p, z⟩, b⟩
  rcases s with ⟨⟨q, w⟩, d⟩
  have detect : ∀ (p q : Klein) (z w : Ternary) (b d : Binary),
      (∀ i : Fin 4, blocks ⟨⟨p, z⟩, b⟩ i = blocks ⟨⟨q, w⟩, d⟩ i) →
        p = q ∧ z = w ∧ b = d := by decide +kernel
  obtain ⟨hp, hz, hb⟩ := detect p q z w b d
    (fun i => congrArg (fun t : Equiv.Perm (Fin 4) => t i) hrs)
  exact SemidirectProduct.ext (SemidirectProduct.ext hp hz) hb

theorem symmetricComplement_card : Nat.card SymmetricComplement = 24 := by
  have hb : Nat.card Binary = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Binary ≃ ZMod 2), Nat.card_zmod]
  rw [Nat.card_congr
      (SemidirectProduct.equivProd : SymmetricComplement ≃ Complement × Binary),
    Nat.card_prod, BinaryFourCanonicalInducedChart.complement_card, hb]

def naturalGroupEquiv : SymmetricComplement ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective blocks ((Nat.bijective_iff_injective_and_card blocks).mpr
    ⟨blocks_injective, by
      rw [symmetricComplement_card]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]⟩)

theorem naturalGroupEquiv_apply (r : SymmetricComplement) (i : Fin 4) :
    naturalGroupEquiv r i = r • i := by rfl

theorem stabilizer_card : Nat.card stabilizer = 6 := by
  have hindex : (MulAction.stabilizer SymmetricComplement (0 : Fin 4)).index = 4 := by
    simpa only [Nat.card_fin] using
      MulAction.index_stabilizer_of_transitive SymmetricComplement (0 : Fin 4)
  change stabilizer.index = 4 at hindex
  have hmul := stabilizer.card_mul_index
  rw [hindex, symmetricComplement_card] at hmul
  omega

/-- The actual canonical point stabilizer acts faithfully on its local
plane. Detection uses two local basis vectors and the fixed physical point. -/
theorem localRepresentation_injective : Function.Injective localRepresentation := by
  intro h k heq
  rcases h with ⟨⟨⟨p, z⟩, b⟩, hh⟩
  rcases k with ⟨⟨⟨q, w⟩, d⟩, hk⟩
  have detect : ∀ (p q : Klein) (z w : Ternary) (b d : Binary),
      blocks ⟨⟨p, z⟩, b⟩ 0 = 0 → blocks ⟨⟨q, w⟩, d⟩ 0 = 0 →
      localLinear ⟨⟨p, z⟩, b⟩ ![1, 0] = localLinear ⟨⟨q, w⟩, d⟩ ![1, 0] →
      localLinear ⟨⟨p, z⟩, b⟩ ![0, 1] = localLinear ⟨⟨q, w⟩, d⟩ ![0, 1] →
      p = q ∧ z = w ∧ b = d := by decide +kernel
  obtain ⟨hp, hz, hb⟩ := detect p q z w b d hh hk
    (congrArg (fun L : _root_.Module.End Scalar Local => L ![1, 0]) heq)
    (congrArg (fun L : _root_.Module.End Scalar Local => L ![0, 1]) heq)
  apply Subtype.ext
  exact SemidirectProduct.ext (SemidirectProduct.ext hp hz) hb

end SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricInducedChart

end
