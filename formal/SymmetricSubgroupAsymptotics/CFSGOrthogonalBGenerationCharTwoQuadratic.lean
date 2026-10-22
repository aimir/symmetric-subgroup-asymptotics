import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationTransposeRootActions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationQuadraticShears
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationQuadraticKernel
import Lean.Elab.Tactic.Omega

/-! Every literal characteristic-two B root preserves the transpose
quadratic form. Closure then preserves it on the actual elementary group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoQuadratic
open CFSGOrthogonalBSerreMatrices
open CFSGOrthogonalBGenerationQuadraticKernel
open CFSGOrthogonalBGenerationQuadraticShears
open CFSGOrthogonalBGenerationTransposeRootActions
variable (K : Type) [Field K] [CharP K 2]

theorem root_preserves_quadratic (r : ℕ) (sgn : Bool) (i : Fin r) (t : K)
    (v : Index r → K) :
    quadratic K (Fin r) ((rootTransvection K r sgn i t : Mat K r)ᵀ *ᵥ v) =
      quadratic K (Fin r) v := by
  by_cases hi : i.val + 1 < r
  · have hn : i ≠ (⟨i.val + 1, hi⟩ : Fin r) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = i.val + 1 at hv
      omega
    cases sgn
    · have hh := congrArg (fun a : K => a + v (middle r) ^ 2)
        (chain_shear (fun j => v (pos r j)) (fun j => v (neg r j))
          i ⟨i.val + 1, hi⟩ hn t)
      unfold quadratic
      simp_rw [positive_chain K r i hi t v]
      simpa [pos, neg, middle] using hh
    · have hh := congrArg (fun a : K => a + v (middle r) ^ 2)
        (chain_shear (fun j => v (pos r j)) (fun j => v (neg r j))
          ⟨i.val + 1, hi⟩ i hn.symm t)
      unfold quadratic
      simp_rw [negative_chain K r i hi t v]
      simpa [pos, neg, middle] using hh
  · cases sgn
    · unfold quadratic
      simp_rw [positive_short K r i hi t v]
      simpa [pos, neg, middle] using
        (short_shear_second (fun j => v (pos r j)) (fun j => v (neg r j))
          (v (middle r)) i t)
    · unfold quadratic
      simp_rw [negative_short K r i hi t v]
      simpa [pos, neg, middle] using
        (short_shear_first (fun j => v (pos r j)) (fun j => v (neg r j))
          (v (middle r)) i t)

theorem elementary_le_transposeIsometries (r : ℕ) :
    elementaryRootGroup K r ≤ transposeIsometries K (Fin r) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨sgn, i, t, rfl⟩
  exact root_preserves_quadratic K r sgn i t

theorem elementary_preserves_quadratic (r : ℕ) (g : elementaryRootGroup K r)
    (v : Index r → K) :
    quadratic K (Fin r) ((g.val : Mat K r)ᵀ *ᵥ v) = quadratic K (Fin r) v :=
  elementary_le_transposeIsometries K r g.property v

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoQuadratic
