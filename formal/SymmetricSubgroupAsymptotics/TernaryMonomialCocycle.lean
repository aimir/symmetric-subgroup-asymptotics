import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeQuotientSocles

/-! Coordinate-dependent ternary signs give an actual linear action and
its affine point action. The cocycle equations are proved by the source
group; no faithfulness or independent-sign assumption is imposed here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace TernaryMonomialCocycle

variable {R X : Type} [Group R]
  (b : R →* Equiv.Perm X) (d : R → X → ZMod 3)
  (hone : ∀ i, d 1 i = 1)
  (hmul : ∀ g h i, d (g * h) i = d g i * d h (b g⁻¹ i))

include hone hmul in
theorem inverse_left (g : R) (i : X) : d g⁻¹ i * d g (b g i) = 1 := by
  have h := hmul g⁻¹ g i
  simpa only [inv_mul_cancel, inv_inv, hone] using h.symm

include hone hmul in
theorem inverse_right (g : R) (i : X) : d g i * d g⁻¹ (b g⁻¹ i) = 1 := by
  have h := hmul g g⁻¹ i
  simpa only [mul_inv_cancel, hone] using h.symm

private theorem index_inv_apply (g : R) (i : X) : b g⁻¹ (b g i) = i := by
  rw [b.map_inv]
  exact (b g).symm_apply_apply i

private theorem index_apply_inv (g : R) (i : X) : b g (b g⁻¹ i) = i := by
  rw [b.map_inv]
  exact (b g).apply_symm_apply i

def linearAction : R →* ((X → ZMod 3) ≃ₗ[ZMod 3] (X → ZMod 3)) where
  toFun g :=
    { toFun := fun v i ↦ d g i * v (b g⁻¹ i)
      invFun := fun v i ↦ d g⁻¹ i * v (b g i)
      left_inv := by
        intro v
        funext i
        change d g⁻¹ i * (d g (b g i) * v (b g⁻¹ (b g i))) = v i
        rw [index_inv_apply, ← mul_assoc, inverse_left b d hone hmul, one_mul]
      right_inv := by
        intro v
        funext i
        change d g i * (d g⁻¹ (b g⁻¹ i) * v (b g (b g⁻¹ i))) = v i
        rw [index_apply_inv, ← mul_assoc, inverse_right b d hone hmul, one_mul]
      map_add' := by intro v w; funext i; exact mul_add _ _ _
      map_smul' := by
        intro a v
        funext i
        change d g i * (a * v (b g⁻¹ i)) = a * (d g i * v (b g⁻¹ i))
        ring }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    funext i
    change d 1 i * v (b (1 : R)⁻¹ i) = v i
    simp only [hone, inv_one, map_one, Equiv.Perm.one_apply, one_mul]
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro v
    funext i
    change d (g * h) i * v (b (g * h)⁻¹ i) =
      d g i * (d h (b g⁻¹ i) * v (b h⁻¹ (b g⁻¹ i)))
    rw [hmul]
    simp only [mul_inv_rev, map_mul, Equiv.Perm.coe_mul, Function.comp_apply, mul_assoc]

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (linearAction b d hone hmul)

def translations : Multiplicative (X → ZMod 3) →* Equiv.Perm (X × ZMod 3) where
  toFun v :=
    { toFun := fun p ↦ (p.1, v.toAdd p.1 + p.2)
      invFun := fun p ↦ (p.1, -v.toAdd p.1 + p.2)
      left_inv := by intro p; apply Prod.ext <;> simp
      right_inv := by intro p; apply Prod.ext <;> simp }
  map_one' := by apply Equiv.ext; intro p; apply Prod.ext <;> simp
  map_mul' := by
    intro v w
    apply Equiv.ext
    intro p
    apply Prod.ext
    · rfl
    · exact add_assoc _ _ _

def complement : R →* Equiv.Perm (X × ZMod 3) where
  toFun g :=
    { toFun := fun p ↦ (b g p.1, d g (b g p.1) * p.2)
      invFun := fun p ↦ (b g⁻¹ p.1, d g⁻¹ (b g⁻¹ p.1) * p.2)
      left_inv := by
        intro p
        apply Prod.ext
        · exact index_inv_apply b g p.1
        · change d g⁻¹ (b g⁻¹ (b g p.1)) * (d g (b g p.1) * p.2) = p.2
          rw [index_inv_apply, ← mul_assoc, inverse_left b d hone hmul, one_mul]
      right_inv := by
        intro p
        apply Prod.ext
        · exact index_apply_inv b g p.1
        · change d g (b g (b g⁻¹ p.1)) * (d g⁻¹ (b g⁻¹ p.1) * p.2) = p.2
          rw [index_apply_inv, ← mul_assoc, inverse_right b d hone hmul, one_mul] }
  map_one' := by
    apply Equiv.ext
    intro p
    apply Prod.ext
    · exact Equiv.congr_fun b.map_one p.1
    · change d 1 (b 1 p.1) * p.2 = p.2
      rw [hone, one_mul]
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro p
    apply Prod.ext
    · exact Equiv.congr_fun (b.map_mul g h) p.1
    · change d (g * h) (b (g * h) p.1) * p.2 =
        d g (b g (b h p.1)) * (d h (b h p.1) * p.2)
      rw [hmul, b.map_mul]
      change (d g (b g (b h p.1)) * d h (b g⁻¹ (b g (b h p.1)))) * p.2 = _
      rw [index_inv_apply, mul_assoc]

def action : Model b d hone hmul →* Equiv.Perm (X × ZMod 3) :=
  SemidirectProduct.lift (translations (X := X)) (complement b d hone hmul) (by
    intro g
    apply MonoidHom.ext
    intro v
    apply Equiv.ext
    intro p
    apply Prod.ext
    · change p.1 = b g (b g⁻¹ p.1)
      exact (index_apply_inv b g p.1).symm
    · change d g p.1 * v.toAdd (b g⁻¹ p.1) + p.2 =
        d g (b g (b g⁻¹ p.1)) *
          (v.toAdd (b g⁻¹ p.1) + d g⁻¹ (b g⁻¹ p.1) * p.2)
      rw [index_apply_inv, mul_add, ← mul_assoc, inverse_right b d hone hmul, one_mul])

end TernaryMonomialCocycle
end SymmetricSubgroupAsymptotics

end
