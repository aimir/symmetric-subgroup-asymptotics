import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticCorrection
import SymmetricSubgroupAsymptotics.CFSGPolarCommonPointPlanes

/-! Quadratic-form version of the generic common-point plane helper.
The actual Q-singularity of the sum is retained independently of polar
self-zero, so this lemma is valid in characteristic two as stated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane
open CFSGPolarCommonPointPlanes CFSGOrthogonalDIndexQuadraticCorrection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem polar_zero_of_singular (Q : QuadraticForm K V) (P : Submodule K V)
    (hP : ∀ x ∈ P, Q x = 0) (x y : V) (hx : x ∈ P) (hy : y ∈ P) :
    Q.polarBilin x y = 0 := by
  change Q (x + y) - Q x - Q y = 0
  rw [hP (x + y) (P.add_mem hx hy), hP x hx, hP y hy]
  ring

theorem quadratic_pairPlane_adjacent_data (Q : QuadraticForm K V)
    (P : Submodule K V) (hP : Module.finrank K P = 2) (hPs : ∀ x ∈ P, Q x = 0)
    (u z : V) (huP : u ∈ P) (hu : u ≠ 0) (hz : Q z = 0) (hzP : z ∉ P)
    (hPz : ∀ x ∈ P, Q.polarBilin x z = 0) :
    P ≠ pairPlane u z ∧ Module.finrank K ↥(P ⊓ pairPlane u z) = 1 ∧
      (∀ x ∈ P ⊔ pairPlane u z, Q x = 0) := by
  have hzB : Q.polarBilin z z = 0 := by
    change QuadraticMap.polar Q z z = 0
    rw [Q.polar_self, hz, smul_zero]
  have hPsB := polar_zero_of_singular Q P hPs
  obtain ⟨hne, hd, _⟩ := pairPlane_adjacent_data Q.polarBilin
    (fun x y => QuadraticMap.polar_comm (Q : V → K) x y)
    P hP (fun x hx y hy => hPsB x y hx hy) u z huP hu hzB hzP hPz
  refine ⟨hne, hd, ?_⟩
  apply singular_sup Q P (pairPlane u z) hPs
  · exact singular_span_pair Q u z (hPs u huP) hz (hPz u huP)
  · intro x hx y hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [map_add, map_smul, hPsB x u hx huP, hPz x hx, smul_zero, add_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane
