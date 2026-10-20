import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeQuotientSocles

/-! Actual affine point actions from a permutation of ternary coordinates
and a scalar character. All maps retain the full original semidirect group. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace TernaryMonomialSemidirect

variable {R X : Type} [Group R]
  (b : R →* Equiv.Perm X) (s : R →* (ZMod 3)ˣ)

def coefficient : R →* ZMod 3 := (Units.coeHom (ZMod 3)).comp s

private theorem coefficient_inv_mul (g : R) :
    coefficient s g⁻¹ * coefficient s g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

private theorem coefficient_mul_inv (g : R) :
    coefficient s g * coefficient s g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

private theorem index_inv_apply (g : R) (i : X) : b g⁻¹ (b g i) = i := by
  rw [b.map_inv]
  exact (b g).symm_apply_apply i

private theorem index_apply_inv (g : R) (i : X) : b g (b g⁻¹ i) = i := by
  rw [b.map_inv]
  exact (b g).apply_symm_apply i

def linearAction : R →* ((X → ZMod 3) ≃ₗ[ZMod 3] (X → ZMod 3)) where
  toFun g :=
    { toFun := fun v i ↦ coefficient s g * v (b g⁻¹ i)
      invFun := fun v i ↦ coefficient s g⁻¹ * v (b g i)
      left_inv := by
        intro v
        funext i
        change coefficient s g⁻¹ * (coefficient s g * v (b g⁻¹ (b g i))) = v i
        rw [index_inv_apply, ← mul_assoc, coefficient_inv_mul, one_mul]
      right_inv := by
        intro v
        funext i
        change coefficient s g * (coefficient s g⁻¹ * v (b g (b g⁻¹ i))) = v i
        rw [index_apply_inv, ← mul_assoc, coefficient_mul_inv, one_mul]
      map_add' := by
        intro v w
        funext i
        exact mul_add _ _ _
      map_smul' := by
        intro a v
        funext i
        change coefficient s g * (a * v (b g⁻¹ i)) =
          a * (coefficient s g * v (b g⁻¹ i))
        ring }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    funext i
    change coefficient s 1 * v (b (1 : R)⁻¹ i) = v i
    simp only [inv_one, map_one, Equiv.Perm.one_apply, one_mul]
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro v
    funext i
    change coefficient s (g * h) * v (b (g * h)⁻¹ i) =
      coefficient s g * (coefficient s h * v (b h⁻¹ (b g⁻¹ i)))
    simp only [mul_inv_rev, map_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      mul_assoc]

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (linearAction b s)

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
    { toFun := fun p ↦ (b g p.1, coefficient s g * p.2)
      invFun := fun p ↦ (b g⁻¹ p.1, coefficient s g⁻¹ * p.2)
      left_inv := by
        intro p
        apply Prod.ext
        · exact index_inv_apply b g p.1
        · change coefficient s g⁻¹ * (coefficient s g * p.2) = p.2
          rw [← mul_assoc, coefficient_inv_mul, one_mul]
      right_inv := by
        intro p
        apply Prod.ext
        · exact index_apply_inv b g p.1
        · change coefficient s g * (coefficient s g⁻¹ * p.2) = p.2
          rw [← mul_assoc, coefficient_mul_inv, one_mul] }
  map_one' := by apply Equiv.ext; intro p; apply Prod.ext <;> simp
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro p
    apply Prod.ext
    · exact Equiv.congr_fun (b.map_mul g h) p.1
    · change coefficient s (g * h) * p.2 = coefficient s g * (coefficient s h * p.2)
      rw [map_mul, mul_assoc]

def action : Model b s →* Equiv.Perm (X × ZMod 3) :=
  SemidirectProduct.lift (translations (X := X)) (complement b s) (by
    intro g
    apply MonoidHom.ext
    intro v
    apply Equiv.ext
    intro p
    apply Prod.ext
    · change p.1 = b g (b g⁻¹ p.1)
      exact (index_apply_inv b g p.1).symm
    · change coefficient s g * v.toAdd (b g⁻¹ p.1) + p.2 =
        coefficient s g * (v.toAdd (b g⁻¹ p.1) + coefficient s g⁻¹ * p.2)
      rw [mul_add, ← mul_assoc, coefficient_mul_inv, one_mul])

theorem action_apply (g : Model b s) (p : X × ZMod 3) :
    action b s g p =
      (b g.right p.1, g.left.toAdd (b g.right p.1) + (s g.right : ZMod 3) * p.2) := rfl

end TernaryMonomialSemidirect
end SymmetricSubgroupAsymptotics

end
