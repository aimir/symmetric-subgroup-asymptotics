import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedPointFixation

/-! Fixed points of one singular space determine the complementary
component of any represented singular point, up to a nonzero scalar.
The scalar is pulled back through the genuine field involution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem hermitian_fixed_projection_proportional
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H)
    (hnondeg : ∀ v ∈ P.val, (∀ w ∈ Z.val, hermitianPair sigma H v w = 0) → v = 0)
    (hfixZ : ∀ Q : SingularPoint sigma H, Q.val ≤ Z.val → f Q = Q)
    (R : SingularPoint sigma H) (x z x' z' : I → K)
    (hx : x ∈ P.val) (hz : z ∈ Z.val) (hx' : x' ∈ P.val) (hz' : z' ∈ Z.val)
    (hx0 : x ≠ 0) (hR : x + z ∈ R.val) (hR0 : x + z ≠ 0)
    (himage : x' + z' ∈ (f R).val) (himage0 : x' + z' ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ x' = a • x := by
  have hn : restrictedHermitianPairing sigma H Z (x + z) ≠ 0 := by
    intro he
    apply hx0
    apply hnondeg x hx
    intro w hw
    have hh := LinearMap.congr_fun he ⟨w, hw⟩
    change hermitianPair sigma H (x + z) w = 0 at hh
    rw [hermitianPair_add_left, Z.property z hz w hw, add_zero] at hh
    exact hh
  obtain ⟨c, hc, he⟩ := restrictedHermitianPairing_proportional sigma H f hf Z hfixZ R
    (x + z) (x' + z') hR himage hR0 himage0 hn
  have hv : x' - sigma.symm c • x ∈ P.val :=
    P.val.sub_mem hx' (P.val.smul_mem (sigma.symm c) hx)
  have hzero : x' - sigma.symm c • x = 0 := hnondeg _ hv (by
    intro w hw
    have hh := LinearMap.congr_fun he ⟨w, hw⟩
    change hermitianPair sigma H (x' + z') w = c * hermitianPair sigma H (x + z) w at hh
    rw [hermitianPair_add_left, hermitianPair_add_left,
      Z.property z' hz' w hw, Z.property z hz w hw, add_zero, add_zero] at hh
    have ha := hermitianPair_add_left sigma H (x' - sigma.symm c • x) (sigma.symm c • x) w
    have hs := hermitianPair_smul sigma H (sigma.symm c) 1 x w
    simp only [one_smul, sigma.apply_symm_apply, mul_one] at hs
    rw [sub_add_cancel, hs, hh] at ha
    exact add_right_cancel (ha.symm.trans (zero_add (c * hermitianPair sigma H x w)).symm))
  refine ⟨sigma.symm c, ?_, sub_eq_zero.mp hzero⟩
  intro h
  exact hc (by simpa only [sigma.apply_symm_apply, map_zero] using congrArg sigma h)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
