import SymmetricSubgroupAsymptotics.SchurTargetExtension

/-! An actual injective target map preserves every selected simple type
and can only increase its socle multiplicity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem schurSocleMultiplicity_le_of_injective_target
    {k R A B X : Type} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module k A] [Module R A] [IsScalarTower k R A]
    [AddCommGroup B] [Module k B] [Module R B] [IsScalarTower k R B]
    [AddCommGroup X] [Module k X] [Module R X] [IsScalarTower k R X]
    [FiniteDimensional k A] [FiniteDimensional k B] [FiniteDimensional k X]
    [IsSimpleModule R X]
    (f : A →ₗ[R] B) (hf : Function.Injective f) :
    schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) ≤
      schurSocleMultiplicity (k := k) (R := R) (A := B) (X := X) := by
  let post : (X →ₗ[R] A) →ₗ[k] (X →ₗ[R] B) :=
    { toFun := fun q ↦ f.comp q
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hp : Function.Injective post := by
    intro q r h
    apply LinearMap.ext
    intro x
    exact hf (LinearMap.congr_fun h x)
  have h := LinearMap.finrank_le_finrank_of_injective (f := post) hp
  rw [schurHom_finrank_eq_multiplicity (k := k) (R := R) (A := A) (X := X),
    schurHom_finrank_eq_multiplicity (k := k) (R := R) (A := B) (X := X)] at h
  letI : Nontrivial X := IsSimpleModule.nontrivial R X
  exact Nat.le_of_mul_le_mul_right h (Module.finrank_pos (R := k) (M := Module.End R X))

end SymmetricSubgroupAsymptotics

end
