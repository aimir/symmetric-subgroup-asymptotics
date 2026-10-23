import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleOrbitFlags
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalRootSupport

/-! A positive original D4 root on which one of the two relative
complement functionals vanishes is a simple root in that orbit. The
proof uses nonnegative coordinates and the generic orthogonal-support
theorem, not a positive-root census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4SimpleOrbitSupport
open CFSGTrialityD4NormTwo CFSGTrialityGeckSimpleOrbitFlags CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateOrthogonalRootSupport
local notation "A" => CartanMatrix.D 4

theorem orbitHeight_sum (a : Bool) (x : Fin 4 → ℤ) :
    orbitHeight a x = ∑ i : Fin 4, if i ∈ orbitWord a then 0 else x i := by
  cases a
  · change x 1 = ∑ i : Fin 4, if i ∈ ([0,2,3] : List (Fin 4)) then 0 else x i
    rw [Fin.sum_univ_four]
    change x 1 = 0 + x 1 + 0 + 0
    simp only [zero_add, add_zero]
  · change x 0 + x 2 + x 3 = ∑ i : Fin 4, if i ∈ ([1] : List (Fin 4)) then 0 else x i
    rw [Fin.sum_univ_four]
    change x 0 + x 2 + x 3 = x 0 + 0 + x 2 + x 3
    simp only [add_zero]

theorem orbitHeight_nonnegative (a : Bool) (x : Fin 4 → ℤ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ orbitHeight a x := by
  rw [orbitHeight_sum]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_rfl
  · exact hx i

theorem orbitHeight_zero_supported (a : Bool) (x : Fin 4 → ℤ)
    (hx : ∀ i, 0 ≤ x i) (hz : orbitHeight a x = 0) :
    ∀ i, i ∉ orbitWord a → x i = 0 := by
  rw [orbitHeight_sum] at hz
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      0 ≤ (if i ∈ orbitWord a then 0 else x i) := by
    intro i _
    split_ifs
    · exact le_rfl
    · exact hx i
  have hs := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz
  intro i hi
  simpa only [if_neg hi] using hs i (Finset.mem_univ i)

theorem orbitWord_orthogonal (a : Bool) (i : Fin 4) (hi : i ∈ orbitWord a)
    (j : Fin 4) (hj : j ∈ orbitWord a) (hij : i ≠ j) : A j i = 0 := by
  cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [orbitWord,CFSGTrialityD4PositiveRootOrbits.cartan_eq,Fin.ext_iff] at *

theorem positive_zero_orbit_root (a : Bool) (k : Roots A)
    (hk : ∀ i, 0 ≤ k.val i) (hz : orbitHeight a k.val = 0) :
    ∃ i ∈ orbitWord a, k = (Index i : Roots A) := by
  obtain ⟨i,hi,he⟩ := positive_root_supported_on_orthogonal_simples A (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite {i | i ∈ orbitWord a}
    (fun i hi j hj hij => orbitWord_orthogonal a i hi j hj hij) k hk
    (orbitHeight_zero_supported a k.val hk hz)
  refine ⟨i,hi,he.trans ?_⟩
  apply Subtype.ext
  rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityD4SimpleOrbitSupport
