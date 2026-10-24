import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A nonzero functional on a finite-dimensional field extension identifies
multiplication coefficients with all base-field linear functionals.
This applies to arbitrary prime-field annihilators, without asserting
linearity over the larger field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.FieldFunctionalMultiplicationDuality

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Multiplication followed by the chosen base-field functional. -/
def multiplicationFunctional (f : Module.Dual F K) : K →ₗ[F] Module.Dual F K where
  toFun a :=
    { toFun := fun x => f (a * x)
      map_add' := by intro x y; rw [mul_add, map_add]
      map_smul' := by
        intro r x
        change f (a * (r • x)) = r • f (a * x)
        rw [mul_smul_comm, map_smul] }
  map_add' := by
    intro a b
    ext x
    change f ((a + b) * x) = f (a * x) + f (b * x)
    rw [add_mul, map_add]
  map_smul' := by
    intro r a
    ext x
    change f ((r • a) * x) = r • f (a * x)
    rw [smul_mul_assoc, map_smul]

@[simp] theorem multiplicationFunctional_apply (f : Module.Dual F K) (a x : K) :
    multiplicationFunctional f a x = f (a * x) := rfl

/-- Division in the extension proves separation; no finiteness is needed. -/
theorem multiplicationFunctional_injective (f : Module.Dual F K) (hf : f ≠ 0) :
    Function.Injective (multiplicationFunctional f) := by
  intro a b he
  by_contra hab
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hz : multiplicationFunctional f (a - b) = 0 := by
    rw [map_sub, he, sub_self]
  apply hf
  ext z
  have hez := congrArg (fun l : Module.Dual F K => l ((a - b)⁻¹ * z)) hz
  simpa only [multiplicationFunctional_apply, LinearMap.zero_apply, ← mul_assoc,
    mul_inv_cancel₀ hd, one_mul] using hez

/-- Equal finite dimensions turn separation into an actual coefficient equivalence. -/
def multiplicationEquiv [Module.Finite F K] (f : Module.Dual F K) (hf : f ≠ 0) :
    K ≃ₗ[F] Module.Dual F K :=
  LinearEquiv.ofBijective (multiplicationFunctional f)
    ⟨multiplicationFunctional_injective f hf,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := F) (V := K)).symm).mp
        (multiplicationFunctional_injective f hf)⟩

@[simp] theorem multiplicationEquiv_apply [Module.Finite F K]
    (f : Module.Dual F K) (hf : f ≠ 0) (a x : K) :
    multiplicationEquiv f hf a x = f (a * x) := rfl

theorem exists_unique_coefficient [Module.Finite F K]
    (f : Module.Dual F K) (hf : f ≠ 0) (l : Module.Dual F K) :
    ∃! a : K, ∀ x : K, l x = f (a * x) := by
  obtain ⟨a, ha⟩ := (multiplicationEquiv f hf).surjective l
  refine ⟨a, ?_, ?_⟩
  · intro x
    exact (congrArg (fun g : Module.Dual F K => g x) ha).symm
  · intro b hb
    apply multiplicationFunctional_injective f hf
    ext x
    exact (hb x).symm.trans (congrArg (fun g : Module.Dual F K => g x) ha).symm

end SymmetricSubgroupAsymptotics.FieldFunctionalMultiplicationDuality
