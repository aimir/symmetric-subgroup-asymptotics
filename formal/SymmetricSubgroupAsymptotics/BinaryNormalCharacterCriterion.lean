import SymmetricSubgroupAsymptotics.BinaryNormalSparseRegistry
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The literal central involution subgroup used by the binary character
entry. Its vector-space dimension is proved from its actual cardinality.
The criterion is the finite menu condition; a character-count envelope is
a separate analytic theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open scoped IsMulCommutative

variable (G : Type*) [Group G]

def binaryCentralOmega : Subgroup (Subgroup.center G) :=
  (powMonoidHom (α := Subgroup.center G) 2).ker

instance binaryCentralOmega_commGroup : CommGroup (binaryCentralOmega G) := inferInstance

instance binaryCentralOmega_module : Module (ZMod 2) (Additive (binaryCentralOmega G)) :=
  AddCommGroup.zmodModule (n := 2) (fun x => by
    apply Additive.toMul.injective
    change x.toMul^2=1
    apply Subtype.ext
    exact x.toMul.property)

def binaryCentralOmegaEquiv : binaryCentralOmega G ≃
    {x : G // x∈Subgroup.center G ∧ x^2=1} where
  toFun x := ⟨x.1.1,x.1.2,congrArg Subtype.val x.2⟩
  invFun x := ⟨⟨x.1,x.2.1⟩,Subtype.ext x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem binaryCentralOmega_card_congr {H : Type*} [Group H] (e : G≃*H) :
    Nat.card (binaryCentralOmega G)=Nat.card (binaryCentralOmega H) := by
  let f : {x:G // x∈Subgroup.center G ∧ x^2=1} ≃
      {y:H // y∈Subgroup.center H ∧ y^2=1} := {
    toFun := fun x => ⟨e x.1,(Subgroup.centerCongr e ⟨x.1,x.2.1⟩).2,by
      rw [←map_pow,x.2.2,map_one]⟩
    invFun := fun x => ⟨e.symm x.1,(Subgroup.centerCongr e.symm ⟨x.1,x.2.1⟩).2,by
      rw [←map_pow,x.2.2,map_one]⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
    right_inv := fun x => Subtype.ext (e.apply_symm_apply x.1) }
  exact Nat.card_congr ((binaryCentralOmegaEquiv G).trans
    (f.trans (binaryCentralOmegaEquiv H).symm))

theorem binaryCentralOmega_finrank [Finite G] (z : ℕ)
    (hcard : Nat.card (binaryCentralOmega G)=2^z) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega G))=z := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (binaryCentralOmega G))
  rw [Nat.card_eq_fintype_card (α := ZMod 2),ZMod.card] at hc
  have ha : Nat.card (Additive (binaryCentralOmega G))=
      Nat.card (binaryCentralOmega G) := Nat.card_congr Additive.toMul
  exact Nat.pow_right_injective (by decide : 1<2) (hc.symm.trans (ha.trans hcard))

structure BinaryNormalCharacterCriterion (w : ℕ) where
  dimension : ℕ
  cardinal : Nat.card (binaryCentralOmega G)=2^dimension
  gap : 38^(8*dimension)<2^w*25^(8*dimension)

namespace BinaryNormalCharacterCriterion
variable {G} {w : ℕ} (C : BinaryNormalCharacterCriterion G w)

def transport {H : Type*} [Group H] (e : G≃*H) :
    BinaryNormalCharacterCriterion H w where
  dimension := C.dimension
  cardinal := (binaryCentralOmega_card_congr G e).symm.trans C.cardinal
  gap := C.gap

theorem exact_dimension [Finite G] :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega G))=C.dimension :=
  binaryCentralOmega_finrank G C.dimension C.cardinal

end BinaryNormalCharacterCriterion
end SymmetricSubgroupAsymptotics
