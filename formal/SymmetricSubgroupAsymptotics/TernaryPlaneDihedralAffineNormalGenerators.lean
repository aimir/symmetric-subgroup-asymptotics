import SymmetricSubgroupAsymptotics.DihedralNormalGenerators

/-! Two normal generators for the actual ternary affine models
`F₃² ⋊ C₄` and `F₃² ⋊ D₈`.  The quarter-turn is irreducible over F₃.
The cyclic and dihedral complement bounds are algebraic; the only finite
checks here concern the nine vectors and the four/eight displayed maps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryPlaneDihedralAffineNormalGenerators

abbrev Vector := AffineModel.V 3 2
abbrev LinearGroup := AffineModel.GLV 3 2
abbrev C4 := Multiplicative (ZMod 4)

def e0 : Vector := ![1, 0]
def e1 : Vector := ![0, 1]

def quarterTurn : LinearGroup where
  toFun v := ![-v 1, v 0]
  invFun v := ![v 1, -v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def reflection : LinearGroup where
  toFun v := ![v 0, -v 1]
  invFun v := ![v 0, -v 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def rotationHom : C4 →* LinearGroup where
  toFun k := quarterTurn ^ k.toAdd.val
  map_one' := rfl
  map_mul' := by
    intro i j
    apply LinearEquiv.ext
    intro v
    revert i j v
    decide +kernel

def dihedralHom : DihedralGroup 4 →* LinearGroup where
  toFun
    | .r i => quarterTurn ^ i.val
    | .sr i => reflection * quarterTurn ^ i.val
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      apply LinearEquiv.ext <;> intro v <;> revert i j v <;> decide +kernel

theorem rotationHom_injective : Function.Injective rotationHom := by
  have hcheck : ∀ i j : C4, rotationHom i e0 = rotationHom j e0 → i = j := by
    decide +kernel
  intro i j hij
  exact hcheck i j (congrArg (fun f : LinearGroup => f e0) hij)

theorem dihedralHom_injective : Function.Injective dihedralHom := by
  have hcheck : ∀ i j : DihedralGroup 4,
      dihedralHom i e0 = dihedralHom j e0 →
      dihedralHom i e1 = dihedralHom j e1 → i = j := by
    decide +kernel
  intro i j hij
  exact hcheck i j (congrArg (fun f : LinearGroup => f e0) hij)
    (congrArg (fun f : LinearGroup => f e1) hij)

def combination (x : Vector) (k : Fin 9) : Vector :=
  (k.val % 3) • x + (k.val / 3) • quarterTurn x

theorem combination_spans : ∀ x : Vector, x ≠ 0 → ∀ y : Vector,
    ∃ k : Fin 9, combination x k = y := by
  decide +kernel

theorem irreducible_of_quarterTurn (R : Subgroup LinearGroup)
    (hJ : quarterTurn ∈ R) : AffineModel.Irreducible R := by
  intro S hS
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hbot
    apply le_antisymm _ bot_le
    intro x hx
    exact AddSubgroup.mem_bot.mpr (h x hx)
  obtain ⟨x, hx, hx0⟩ := hx
  apply top_unique
  intro y _hy
  obtain ⟨k, hk⟩ := combination_spans x hx0 y
  rw [← hk]
  exact S.add_mem (S.nsmul_mem hx _) (S.nsmul_mem (hS quarterTurn hJ x hx) _)

theorem rotationHom_one : rotationHom (Multiplicative.ofAdd 1) = quarterTurn := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem dihedralHom_r_one : dihedralHom (.r 1) = quarterTurn := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

def linearAction {H : Type} [Group H] (f : H →* LinearGroup) :
    H →* MulAut (Multiplicative Vector) :=
  (AffineModel.linAut f.range).comp f.rangeRestrict

abbrev ModelFour := Multiplicative Vector ⋊[linearAction rotationHom] C4
abbrev ModelEight := Multiplicative Vector ⋊[linearAction dihedralHom] DihedralGroup 4

/-- This equivalence identifies the displayed coordinates with the faithful
affine model of the actual image, retaining its exact linear action. -/
def modelEquiv {H : Type} [Group H] (f : H →* LinearGroup)
    (hf : Function.Injective f) :
    Multiplicative Vector ⋊[linearAction f] H ≃* AffineModel.Aff f.range :=
  SemidirectProduct.congr (MulEquiv.refl _) (MonoidHom.ofInjective hf) (by
    intro h
    apply MulEquiv.ext
    intro v
    rfl)

theorem model_normal_generating_pairs {H : Type} [Group H]
    (f : H →* LinearGroup) (hf : Function.Injective f)
    (hJ : quarterTurn ∈ f.range)
    (hH : ∀ N : Subgroup H, N.Normal →
      ∃ x : Fin 2 → H, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (Multiplicative Vector ⋊[linearAction f] H), N.Normal →
      ∃ x : Fin 2 → Multiplicative Vector ⋊[linearAction f] H,
        Subgroup.normalClosure (Set.range x) = N := by
  have hR := normal_generating_tuples_of_surjective f.rangeRestrict
    f.rangeRestrict_surjective hH
  have hAff := AffineModel.normal_generating_tuples_of_irreducible_complement
    f.range (irreducible_of_quarterTurn f.range hJ) e0 (by decide +kernel)
    (by decide : 0 < 2) hR
  exact normal_generating_tuples_of_surjective (modelEquiv f hf).symm.toMonoidHom
    (modelEquiv f hf).symm.surjective hAff

theorem modelFour_normal_generating_pairs :
    ∀ N : Subgroup ModelFour, N.Normal →
      ∃ x : Fin 2 → ModelFour, Subgroup.normalClosure (Set.range x) = N :=
  model_normal_generating_pairs rotationHom rotationHom_injective
    ⟨Multiplicative.ofAdd 1, rotationHom_one⟩
    (normal_generating_pairs_of_cyclic_kernel (MonoidHom.id C4))

theorem modelEight_normal_generating_pairs :
    ∀ N : Subgroup ModelEight, N.Normal →
      ∃ x : Fin 2 → ModelEight, Subgroup.normalClosure (Set.range x) = N :=
  model_normal_generating_pairs dihedralHom dihedralHom_injective
    ⟨DihedralGroup.r 1, dihedralHom_r_one⟩
    (DihedralNormalGenerators.normal_generating_pairs 4)

end TernaryPlaneDihedralAffineNormalGenerators
end SymmetricSubgroupAsymptotics

end
