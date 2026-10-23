import SymmetricSubgroupAsymptotics.CFSGHermitianPointFunctionals
import Mathlib.Tactic.LinearCombination

/-! A fixed singular space and a stabilized opposite with nondegenerate
cross pairing force pointwise fixation of that opposite. The coefficient
on the original vector is sigma inverse of the functional coefficient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem hermitian_fixes_opposite_of_pairing_nondegenerate
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (S Z : IsotropicSpace sigma H)
    (hnondeg : ∀ v ∈ Z.val, (∀ w ∈ S.val, hermitianPair sigma H v w = 0) → v = 0)
    (hfix : ∀ Q : SingularPoint sigma H, Q.val ≤ S.val → f Q = Q)
    (hstable : ∀ P : SingularPoint sigma H, P.val ≤ Z.val → (f P).val ≤ Z.val) :
    ∀ P : SingularPoint sigma H, P.val ≤ Z.val → f P = P := by
  intro P hP
  obtain ⟨x, hx, hx0⟩ := singularPoint_nonzero sigma H P
  obtain ⟨y, hy, hy0⟩ := singularPoint_nonzero sigma H (f P)
  have hn : restrictedHermitianPairing sigma H S x ≠ 0 := by
    intro hz
    apply hx0
    exact hnondeg x (hP hx) (fun w hw => LinearMap.congr_fun hz ⟨w, hw⟩)
  obtain ⟨c, _, he⟩ := restrictedHermitianPairing_proportional sigma H f hf S hfix P x y hx hy hx0 hy0 hn
  have hv : y - sigma.symm c • x ∈ Z.val :=
    Z.val.sub_mem (hstable P hP hy) (Z.val.smul_mem (sigma.symm c) (hP hx))
  have hz : y - sigma.symm c • x = 0 := hnondeg _ hv (by
    intro w hw
    have hh := LinearMap.congr_fun he ⟨w, hw⟩
    change hermitianPair sigma H y w = c * hermitianPair sigma H x w at hh
    have ha := hermitianPair_add_left sigma H (y - sigma.symm c • x) (sigma.symm c • x) w
    have hs := hermitianPair_smul sigma H (sigma.symm c) 1 x w
    simp only [one_smul, sigma.apply_symm_apply, mul_one] at hs
    rw [sub_add_cancel, hs] at ha
    rw [hh] at ha
    exact add_right_cancel (ha.symm.trans (zero_add (c * hermitianPair sigma H x w)).symm))
  have hyP : y ∈ P.val := (sub_eq_zero.mp hz) ▸ P.val.smul_mem (sigma.symm c) hx
  apply Subtype.ext
  exact (singularPoint_span sigma H (f P) y hy hy0).trans
    (singularPoint_span sigma H P y hyP hy0).symm

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
