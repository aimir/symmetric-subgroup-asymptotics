import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Span.Basic

/-! Singular spanning and nondegeneracy supply a singular vector with
polar pairing exactly one against any given nonzero vector. Scaling
occurs before any group action, so no torus or square-root premise is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.QuadraticSingularSpanPairing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_singular_nonorthogonal (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate)
    (hspan : Submodule.span K {u : V | Q u = 0} = ⊤)
    (v : V) (hv : v ≠ 0) : ∃ u : V, Q u = 0 ∧ Q.polarBilin u v ≠ 0 := by
  by_contra h
  apply hv
  apply hQ.2
  intro u
  have hle : Submodule.span K {w : V | Q w = 0} ≤
      LinearMap.ker (Q.polarBilin.flip v) := by
    apply Submodule.span_le.mpr
    intro w hw
    change Q.polarBilin w v = 0
    by_contra hne
    exact h ⟨w, hw, hne⟩
  rw [hspan] at hle
  exact hle (show u ∈ (⊤ : Submodule K V) from trivial)

theorem exists_singular_pairing_one (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate)
    (hspan : Submodule.span K {u : V | Q u = 0} = ⊤)
    (v : V) (hv : v ≠ 0) :
    ∃ u : V, u ≠ 0 ∧ Q u = 0 ∧ Q.polarBilin u v = 1 := by
  obtain ⟨w, hw, hne⟩ := exists_singular_nonorthogonal Q hQ hspan v hv
  let u := (Q.polarBilin w v)⁻¹ • w
  have huQ : Q u = 0 := by
    dsimp only [u]
    rw [Q.map_smul, hw, smul_zero]
  have hu : Q.polarBilin u v = 1 := by
    change (Q.polarBilin ((Q.polarBilin w v)⁻¹ • w)) v = 1
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne]
  refine ⟨u, ?_, huQ, hu⟩
  intro hz
  have hh : (0 : K) = 1 := by simpa only [hz, map_zero, LinearMap.zero_apply] using hu
  exact zero_ne_one hh

end SymmetricSubgroupAsymptotics.QuadraticSingularSpanPairing
