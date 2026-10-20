import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.PGroup

/-!
# The actual zero-sum binary kernel of row 32

The original twelve points are three regular Klein-four blocks. The
binary translations have shifts `(a,b,a+b)` and the cubic generator
cyclically permutes the blocks. An explicit semidirect-product chart
binds the original three generators and short words cover its parameters.
This gives the literal top a binary normal kernel of order sixteen,
without enumerating the subgroup of `S₁₂` or any of its normal subgroups.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow32BinaryChart

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SemidirectProduct

abbrev Four := ZMod 2 × ZMod 2
abbrev Translation := Multiplicative (Four × Four)
abbrev Cubic := Multiplicative (ZMod 3)
abbrev Points := ZMod 3 × Four
abbrev Top := Row32Top

private def rotate (c : Cubic) (v : Translation) : Translation :=
  Multiplicative.ofAdd <|
    if c.toAdd = 0 then v.toAdd
    else if c.toAdd = 1 then (v.toAdd.1 + v.toAdd.2, v.toAdd.1)
    else (v.toAdd.2, v.toAdd.1 + v.toAdd.2)

def rotation : Cubic →* MulAut Translation where
  toFun c :=
    { toFun := rotate c
      invFun := rotate c⁻¹
      left_inv := by decide +kernel +revert
      right_inv := by decide +kernel +revert
      map_mul' := by decide +kernel +revert }
  map_one' := by
    apply MulEquiv.ext
    intro v
    rfl
  map_mul' := by
    intro c d
    apply MulEquiv.ext
    intro v
    revert c d v
    decide +kernel

abbrev Model := Translation ⋊[rotation] Cubic

instance modelFintype : Fintype Model :=
  Fintype.ofEquiv (Translation × Cubic) SemidirectProduct.equivProd.symm

private def shift (v : Translation) (i : ZMod 3) : Four :=
  if i = 0 then v.toAdd.1 else if i = 1 then v.toAdd.2 else v.toAdd.1 + v.toAdd.2

private def act (g : Model) (p : Points) : Points :=
  (g.right.toAdd + p.1, shift g.left (g.right.toAdd + p.1) + p.2)

def modelAction : Model →* Equiv.Perm Points where
  toFun g :=
    { toFun := act g
      invFun := act g⁻¹
      left_inv := by decide +kernel +revert
      right_inv := by decide +kernel +revert }
  map_one' := by
    apply Equiv.ext
    intro p
    revert p
    decide +kernel
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro p
    revert g h p
    decide +kernel

theorem modelAction_injective : Function.Injective modelAction := by
  intro g h he
  have hc : ∀ g h : Model, (∀ p : Points, modelAction g p = modelAction h p) → g = h := by
    decide +kernel
  exact hc g h (fun p ↦ Equiv.congr_fun he p)

/-- This is the point chart already used by the nine-dimensional
augmentation certificate, with local points written as two binary bits. -/
def pointEquiv : Fin 12 ≃ Points where
  toFun := ![(0, (0, 0)), (1, (1, 0)), (2, (0, 1)), (0, (1, 1)),
    (1, (0, 0)), (2, (1, 0)), (0, (0, 1)), (1, (1, 1)),
    (2, (0, 0)), (0, (1, 0)), (1, (0, 1)), (2, (1, 1))]
  invFun p := if p.2.1 = 0 then
      if p.2.2 = 0 then (#[0, 4, 8] : Array (Fin 12))[p.1.val]!
      else (#[6, 10, 2] : Array (Fin 12))[p.1.val]!
    else if p.2.2 = 0 then (#[9, 1, 5] : Array (Fin 12))[p.1.val]!
      else (#[3, 7, 11] : Array (Fin 12))[p.1.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalAction : Model →* Equiv.Perm (Fin 12) :=
  pointEquiv.symm.permCongrHom.toMonoidHom.comp modelAction

theorem literalAction_injective : Function.Injective literalAction :=
  pointEquiv.symm.permCongrHom.injective.comp modelAction_injective

def modelGenerators : Fin 3 → Model :=
  ![inl (Multiplicative.ofAdd ((1, 0), (0, 0))),
    inl (Multiplicative.ofAdd ((0, 1), (0, 0))),
    inr (Multiplicative.ofAdd 1)]

theorem generators_binding (i : Fin 3) :
    literalAction (modelGenerators i) = row32Generators i := by
  ext x
  revert i x
  decide +kernel

/-- Four binary exponents and one cubic exponent are original generator
words for every vector parameter in the explicit model. -/
theorem model_word_cover (g : Model) :
    ∃ a b c d : Fin 2, ∃ r : Fin 3,
      g = modelGenerators 0 ^ a.val * modelGenerators 1 ^ b.val *
        (modelGenerators 2 * modelGenerators 0 * (modelGenerators 2)⁻¹) ^ c.val *
        (modelGenerators 2 * modelGenerators 1 * (modelGenerators 2)⁻¹) ^ d.val *
        modelGenerators 2 ^ r.val := by
  refine ⟨⟨(g.left.toAdd.1.1 + g.left.toAdd.2.1).val, ZMod.val_lt _⟩,
    ⟨(g.left.toAdd.1.2 + g.left.toAdd.2.2).val, ZMod.val_lt _⟩,
    ⟨g.left.toAdd.2.1.val, ZMod.val_lt _⟩,
    ⟨g.left.toAdd.2.2.val, ZMod.val_lt _⟩,
    ⟨g.right.toAdd.val, ZMod.val_lt _⟩, ?_⟩
  revert g
  decide +kernel

theorem literalAction_range : literalAction.range = Top := by
  apply le_antisymm
  · have hgen (i : Fin 3) : literalAction (modelGenerators i) ∈ Top := by
      rw [generators_binding]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    have hconj (i : Fin 3) :
        literalAction (modelGenerators 2 * modelGenerators i * (modelGenerators 2)⁻¹)
          ∈ Top := by
      rw [map_mul, map_mul, map_inv]
      exact Top.mul_mem (Top.mul_mem (hgen 2) (hgen i)) (Top.inv_mem (hgen 2))
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, b, c, d, r, hg⟩ := model_word_cover g
    rw [hg, map_mul, map_mul, map_mul, map_mul,
      map_pow, map_pow, map_pow, map_pow, map_pow]
    exact Top.mul_mem
      (Top.mul_mem
        (Top.mul_mem (Top.mul_mem (Top.pow_mem (hgen 0) a.val)
          (Top.pow_mem (hgen 1) b.val)) (Top.pow_mem (hconj 0) c.val))
        (Top.pow_mem (hconj 1) d.val)) (Top.pow_mem (hgen 2) r.val)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : Model ≃* Top :=
  (MonoidHom.ofInjective literalAction_injective).trans
    (MulEquiv.subgroupCongr literalAction_range)

def beta : Top →* Cubic :=
  (rightHom : Model →* Cubic).comp modelEquiv.symm.toMonoidHom

theorem beta_surjective : Function.Surjective beta :=
  rightHom_surjective.comp modelEquiv.symm.surjective

def binaryKernelEquiv : Translation ≃* beta.ker := by
  let i : Translation →* Top := modelEquiv.toMonoidHom.comp inl
  have hi : Function.Injective i := modelEquiv.injective.comp inl_injective
  have hrange : i.range = beta.ker := by
    ext g
    constructor
    · rintro ⟨v, rfl⟩
      change rightHom (modelEquiv.symm (modelEquiv (inl v))) = 1
      rw [modelEquiv.symm_apply_apply, rightHom_inl]
    · intro hg
      change (modelEquiv.symm g).right = 1 at hg
      refine ⟨(modelEquiv.symm g).left, ?_⟩
      change modelEquiv (inl (modelEquiv.symm g).left) = g
      apply modelEquiv.symm.injective
      rw [modelEquiv.symm_apply_apply]
      apply SemidirectProduct.ext
      · rfl
      · exact hg.symm
  exact (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hrange)

theorem binaryKernel_card : Nat.card beta.ker = 16 := by
  rw [← Nat.card_congr binaryKernelEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

theorem binaryKernel_isPGroup : IsPGroup 2 beta.ker :=
  IsPGroup.of_card (n := 4) (by simpa using binaryKernel_card)

theorem binaryKernel_pow_two (g : beta.ker) : g ^ 2 = 1 := by
  apply binaryKernelEquiv.symm.injective
  rw [map_pow, map_one]
  have h : ∀ v : Translation, v ^ 2 = 1 := by decide +kernel
  exact h _

end PrimitiveAffineDegreeTwoTwelveRow32BinaryChart
end SymmetricSubgroupAsymptotics

end
