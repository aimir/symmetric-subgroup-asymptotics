import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryGroup

/-! Literal quadratic B root elements, with additive parameters and
their original defining-family coverage in the actual natural subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements
open Matrix CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K]

def rootElement (r : ℕ) (neg : Bool) (i : Fin r) (a : K) : elementaryRootGroup K r :=
  ⟨rootTransvection K r neg i a, rootTransvection_mem K r neg i a⟩

@[simp] theorem rootElement_zero (r : ℕ) (neg : Bool) (i : Fin r) :
    rootElement K r neg i 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change 1 + (0 : K) • rootMatrix K r neg i + (0 : K) ^ 2 • rootSecond K r neg i = 1
  simp

theorem rootElement_add (r : ℕ) (neg : Bool) (i : Fin r) (a b : K) :
    rootElement K r neg i (a + b) = rootElement K r neg i a * rootElement K r neg i b := by
  apply Subtype.ext
  apply Units.ext
  change 1 + (a + b) • rootMatrix K r neg i + (a + b) ^ 2 • rootSecond K r neg i =
    (1 + a • rootMatrix K r neg i + a ^ 2 • rootSecond K r neg i) *
      (1 + b • rootMatrix K r neg i + b ^ 2 • rootSecond K r neg i)
  simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
    smul_smul, rootMatrix_square, rootMatrix_mul_second, rootSecond_mul_matrix,
    rootSecond_square, smul_zero, add_zero, zero_add, smul_add]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem rootElement_inv (r : ℕ) (neg : Bool) (i : Fin r) (a : K) :
    (rootElement K r neg i a)⁻¹ = rootElement K r neg i (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← rootElement_add, add_neg_cancel, rootElement_zero]

theorem rootElements_generate (r : ℕ) :
    Subgroup.closure {u : elementaryRootGroup K r | ∃ neg i a, u = rootElement K r neg i a} = ⊤ := by
  let H := Subgroup.closure {u : elementaryRootGroup K r | ∃ neg i a, u = rootElement K r neg i a}
  have hle : elementaryRootGroup K r ≤ H.map (elementaryRootGroup K r).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨neg, i, a, rfl⟩
    exact ⟨rootElement K r neg i a, Subgroup.subset_closure ⟨neg, i, a, rfl⟩, rfl⟩
  apply top_unique
  intro u _
  obtain ⟨v, hv, he⟩ := hle u.property
  exact (Subtype.ext he : v = u) ▸ hv

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements
