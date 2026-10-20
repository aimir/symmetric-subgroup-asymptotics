import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles

/-! The fixed four-bit affine chart, with translations recovered from
irreducibility and one original nonzero translation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourAffineImage

abbrev Vector := AffineModel.V 2 4
abbrev LinearGroup := AffineModel.GLV 2 4
abbrev pointEquiv := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.pointEquiv
abbrev linearPerm := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm
abbrev translationPerm := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translationPerm

def action (R : Subgroup LinearGroup) : AffineModel.Aff R →* Equiv.Perm (Fin 16) :=
  pointEquiv.permCongrHom.toMonoidHom.comp (AffineModel.action R)

theorem action_injective (R : Subgroup LinearGroup) : Function.Injective (action R) :=
  pointEquiv.permCongrHom.injective.comp (AffineModel.action_injective R)

theorem action_inl (R : Subgroup LinearGroup) (v : Multiplicative Vector) :
    action R (SemidirectProduct.inl v) = translationPerm v := by
  apply Equiv.ext
  intro x
  rfl

theorem action_inr (R : Subgroup LinearGroup) (r : R) :
    action R (SemidirectProduct.inr r) = linearPerm r.1 := by
  apply Equiv.ext
  intro x
  change pointEquiv (0 + r.1 (pointEquiv.symm x)) = pointEquiv (r.1 (pointEquiv.symm x))
  rw [zero_add]

theorem linearPerm_mem_of_closure {I : Type} (g : I → LinearGroup)
    (H : Subgroup (Equiv.Perm (Fin 16))) (hg : ∀ i, linearPerm (g i) ∈ H)
    {r : LinearGroup} (hr : r ∈ Subgroup.closure (Set.range g)) : linearPerm r ∈ H := by
  induction hr using Subgroup.closure_induction with
  | mem r hr => obtain ⟨i, rfl⟩ := hr; exact hg i
  | one => simpa only [map_one] using H.one_mem
  | mul r s _ _ hr hs => simpa only [map_mul] using H.mul_mem hr hs
  | inv r _ hr => simpa only [map_inv] using H.inv_mem hr

/-- One nonzero translation and the actual irreducible linear subgroup
force every translation into the original permutation subgroup. -/
theorem translation_mem_of_irreducible
    (R : Subgroup LinearGroup) (hirr : AffineModel.Irreducible R)
    (H : Subgroup (Equiv.Perm (Fin 16)))
    (hlinear : ∀ r ∈ R, linearPerm r ∈ H)
    (v₀ : Vector) (hv₀ : v₀ ≠ 0)
    (ht : translationPerm (Multiplicative.ofAdd v₀) ∈ H)
    (v : Multiplicative Vector) : translationPerm v ∈ H := by
  let S : AddSubgroup Vector := {
    carrier := {w | translationPerm (Multiplicative.ofAdd w) ∈ H}
    zero_mem' := by
      change translationPerm (Multiplicative.ofAdd (0 : Vector)) ∈ H
      rw [ofAdd_zero, map_one]
      exact H.one_mem
    add_mem' := by
      intro x y hx hy
      change translationPerm (Multiplicative.ofAdd (x + y)) ∈ H
      rw [ofAdd_add, map_mul]
      exact H.mul_mem hx hy
    neg_mem' := by
      intro x hx
      change translationPerm (Multiplicative.ofAdd (-x)) ∈ H
      rw [ofAdd_neg, map_inv]
      exact H.inv_mem hx }
  have hstable : ∀ r ∈ R, ∀ w ∈ S, r w ∈ S := by
    intro r hr w hw
    have hconj : linearPerm r * translationPerm (Multiplicative.ofAdd w) *
        (linearPerm r)⁻¹ = translationPerm (Multiplicative.ofAdd (r w)) := by
      simpa only [map_mul, map_inv, action_inl, action_inr,
        SemidirectProduct.right_inr, AffineModel.linAut_apply] using
        congrArg (action R)
          (AffineModel.conj_inl R (SemidirectProduct.inr (⟨r, hr⟩ : R))
            (Multiplicative.ofAdd w))
    change translationPerm (Multiplicative.ofAdd (r w)) ∈ H
    rw [← hconj]
    exact H.mul_mem (H.mul_mem (hlinear r hr) hw) (H.inv_mem (hlinear r hr))
  rcases hirr S hstable with hbot | htop
  · have hv : v₀ ∈ S := ht
    rw [hbot] at hv
    exact (hv₀ (AddSubgroup.mem_bot.mp hv)).elim
  · have hv : v.toAdd ∈ S := by rw [htop]; exact AddSubgroup.mem_top _
    exact hv

theorem action_range_le
    (R : Subgroup LinearGroup) (H : Subgroup (Equiv.Perm (Fin 16)))
    (ht : ∀ v, translationPerm v ∈ H)
    (hl : ∀ r ∈ R, linearPerm r ∈ H) : (action R).range ≤ H := by
  rintro _ ⟨g, rfl⟩
  rw [← SemidirectProduct.inl_left_mul_inr_right g, map_mul, action_inl, action_inr]
  exact H.mul_mem (ht g.left) (hl g.right.1 g.right.2)

end BinaryFourAffineImage
end SymmetricSubgroupAsymptotics

end
