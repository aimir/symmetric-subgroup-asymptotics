import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightCoordinateAction
import Mathlib.Tactic.Group

/-! Actual invariant coordinate subspaces pull back to ambient normal
translation subgroups. Primitivity forces each to be zero or the whole
space, retaining the specified degree-eight chart and matrix map. -/

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix IsMulCommutative

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [MulAction L Ω]
  [Finite L] [Finite Ω] [Nontrivial Ω]
  (P : PrimitiveAffineProfile L Ω)

private theorem degreeEight_conjugate_translation
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (u : P.V ⋊[P.complementAction x] P.complement x) (v : P.V) :
    P.semidirectEquiv x u * (v : L) * (P.semidirectEquiv x u)⁻¹ =
      (P.complementAction x u.right v : L) := by
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  have hcomm := congrArg Subtype.val
    (mul_comm u.left (P.complementAction x u.right v))
  change (u.left : L) * ((u.right : L) * (v : L) * (u.right : L)⁻¹) =
    ((u.right : L) * (v : L) * (u.right : L)⁻¹) * (u.left : L) at hcomm
  change ((u.left : L) * (u.right : L)) * (v : L) *
      ((u.left : L) * (u.right : L))⁻¹ =
    (u.right : L) * (v : L) * (u.right : L)⁻¹
  calc
    _ = (u.left : L) * ((u.right : L) * (v : L) * (u.right : L)⁻¹) *
        (u.left : L)⁻¹ := by group
    _ = _ := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

private def degreeEight_invariantTranslations (_x : Ω)
    (a : P.V ≃* Multiplicative (Fin 3 → ZMod 2))
    (W : Submodule (ZMod 2) (Fin 3 → ZMod 2)) : Subgroup P.V where
  carrier := {v | (a v).toAdd ∈ W}
  one_mem' := by simpa using W.zero_mem
  mul_mem' := by
    intro u v hu hv
    change (a (u * v)).toAdd ∈ W
    rw [map_mul]
    exact W.add_mem hu hv
  inv_mem' := by
    intro v hv
    change (a v⁻¹).toAdd ∈ W
    rw [map_inv]
    exact W.neg_mem hv

theorem invariantCoordinateSubmodule_eq_bot_or_top
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 3 → ZMod 2))
    (W : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (hstable : ∀ k : P.complement x, ∀ v ∈ W,
      (P.complementCoordinateMap x a k).val *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  let K₀ : Subgroup P.V := degreeEight_invariantTranslations P x a W
  let K : Subgroup L := K₀.map P.V.subtype
  have hKnormal : K.Normal := by
    constructor
    intro y hy q
    obtain ⟨v, hv, rfl⟩ := hy
    obtain ⟨u, rfl⟩ := (P.semidirectEquiv x).surjective q
    refine ⟨P.complementAction x u.right v, ?_,
      (degreeEight_conjugate_translation P hprimitive x u v).symm⟩
    change (a (P.complementAction x u.right v)).toAdd ∈ W
    rw [← P.complementCoordinateMap_action x a u.right v]
    exact hstable u.right (a v).toAdd hv
  have hKle : K ≤ P.V := Subgroup.map_subtype_le K₀
  have hK := P.minimal hprimitive K hKnormal hKle
  have hK₀ : K₀ = ⊥ ∨ K₀ = ⊤ := by
    rcases hK with hbot | htop
    · exact Or.inl ((K₀.map_eq_bot_iff_of_injective P.V.subtype_injective).mp hbot)
    · right
      apply Subgroup.map_injective P.V.subtype_injective
      simpa only [K, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using htop
  rcases hK₀ with hbot | htop
  · left
    apply eq_bot_iff.mpr
    intro v hv
    let t : P.V := a.symm (Multiplicative.ofAdd v)
    have ht : t ∈ K₀ := by
      change (a t).toAdd ∈ W
      simpa [t] using hv
    rw [hbot] at ht
    have ht1 : t = 1 := Subgroup.mem_bot.mp ht
    apply (Submodule.mem_bot (R := ZMod 2)).mpr
    have he := congrArg (fun t : P.V => (a t).toAdd) ht1
    simpa [t] using he
  · right
    apply top_le_iff.mp
    intro v _
    let t : P.V := a.symm (Multiplicative.ofAdd v)
    have ht : t ∈ K₀ := by rw [htop]; exact Subgroup.mem_top t
    change (a t).toAdd ∈ W at ht
    simpa [t] using ht

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

end
