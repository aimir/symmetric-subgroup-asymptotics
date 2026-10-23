import SymmetricSubgroupAsymptotics.CFSGHermitianPointFunctionals

/-! Fixed singular-point tests determine a nondegenerate component even
with an orthogonal remainder. This retains the anisotropic middle term
in odd ambient dimension rather than treating it as a singular vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem hermitian_fixed_projection_with_remainder
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P : Submodule K (I → K)) (Z : IsotropicSpace sigma H)
    (hND : ∀ x ∈ P, (∀ y ∈ Z.val, hermitianPair sigma H x y = 0) → x = 0)
    (hfixZ : ∀ Q : SingularPoint sigma H, Q.val ≤ Z.val → f Q = Q)
    (R : SingularPoint sigma H) (x r x' r' : I → K)
    (hx : x ∈ P) (hx' : x' ∈ P)
    (hr : ∀ z ∈ Z.val, hermitianPair sigma H r z = 0)
    (hr' : ∀ z ∈ Z.val, hermitianPair sigma H r' z = 0)
    (hx0 : x ≠ 0) (hR : x + r ∈ R.val) (hR0 : x + r ≠ 0)
    (himage : x' + r' ∈ (f R).val) (himage0 : x' + r' ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ x' = a • x := by
  have hn : restrictedHermitianPairing sigma H Z (x + r) ≠ 0 := by
    intro he
    apply hx0
    apply hND x hx
    intro z hz
    have hh := LinearMap.congr_fun he ⟨z, hz⟩
    change hermitianPair sigma H (x + r) z = 0 at hh
    rw [hermitianPair_add_left, hr z hz, add_zero] at hh
    exact hh
  obtain ⟨c, hc, he⟩ := restrictedHermitianPairing_proportional sigma H f hf Z hfixZ R
    (x + r) (x' + r') hR himage hR0 himage0 hn
  have hv : x' - sigma.symm c • x ∈ P := P.sub_mem hx' (P.smul_mem (sigma.symm c) hx)
  have hzero : x' - sigma.symm c • x = 0 := hND _ hv (by
    intro z hz
    have hh := LinearMap.congr_fun he ⟨z, hz⟩
    change hermitianPair sigma H (x' + r') z = c * hermitianPair sigma H (x + r) z at hh
    rw [hermitianPair_add_left, hermitianPair_add_left, hr z hz, hr' z hz, add_zero, add_zero] at hh
    have ha := hermitianPair_add_left sigma H (x' - sigma.symm c • x) (sigma.symm c • x) z
    have hs := hermitianPair_smul sigma H (sigma.symm c) 1 x z
    simp only [one_smul, sigma.apply_symm_apply, mul_one] at hs
    rw [sub_add_cancel, hs, hh] at ha
    exact add_right_cancel (ha.symm.trans (zero_add (c * hermitianPair sigma H x z)).symm))
  refine ⟨sigma.symm c, ?_, sub_eq_zero.mp hzero⟩
  intro h
  exact hc (by simpa only [sigma.apply_symm_apply, map_zero] using congrArg sigma h)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
