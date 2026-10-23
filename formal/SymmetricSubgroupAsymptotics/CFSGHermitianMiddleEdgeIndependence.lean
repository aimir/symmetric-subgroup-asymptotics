import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.LinearCombination

/-! Two distinct normalized outside vectors on a singular generator
line have independent half-projections. The anisotropic half-norm
excludes the otherwise possible proportional-projection obstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem hermitian_middle_edge_independent (sigma : K ≃+* K) (H : Matrix I I K)
    (p q h : I → K) (hp : hermitianPair sigma H p p ≠ 0) (hpq : p ≠ q)
    (hph : hermitianPair sigma H p h = 0) (hhp : hermitianPair sigma H h p = 0)
    (hn : hermitianPair sigma H (p + h) (p + h) = 0)
    (he : hermitianPair sigma H (p + h) (q + h) = 0) : LinearIndependent K ![p,q] := by
  have hp0 : p ≠ 0 := by
    intro hz
    exact hp (by rw [hz]; exact pair_zero_left _ _ _)
  apply (LinearIndependent.pair_iff' hp0).mpr
  intro c hc
  have hn' : hermitianPair sigma H p p + hermitianPair sigma H h h = 0 := by
    rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right, hph, hhp] at hn
    simpa only [add_zero, zero_add] using hn
  have hpc := hermitianPair_smul sigma H 1 c p p
  have hhcp := hermitianPair_smul sigma H 1 c h p
  simp only [one_smul, map_one, one_mul] at hpc hhcp
  have he' : c * hermitianPair sigma H p p + hermitianPair sigma H h h = 0 := by
    rw [←hc, hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
      hpc, hhcp, hph, hhp, mul_zero] at he
    simpa only [add_zero, zero_add] using he
  have hprod : (c - 1) * hermitianPair sigma H p p = 0 := by
    linear_combination he' - hn'
  have hc1 : c = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hp)
  exact hpq (by simpa only [hc1, one_smul] using hc)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
