import SymmetricSubgroupAsymptotics.CFSGHermitianPointFunctionals
import SymmetricSubgroupAsymptotics.CFSGTwoFunctionalPrescription

/-! Independent vectors prescribe any two cross-pairing values on a
nondegenerate opposite space. There is no rank-two, finite-field, or
surjective ambient-duality hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem independent_hermitian_pair_values (sigma : K ≃+* K) (H : Matrix I I K)
    (P Z : Submodule K (I → K))
    (hND : ∀ x ∈ P, (∀ z ∈ Z, hermitianPair sigma H x z = 0) → x = 0)
    (x u : I → K) (hx : x ∈ P) (hu : u ∈ P)
    (hli : LinearIndependent K ![x,u]) (a b : K) :
    ∃ z ∈ Z, hermitianPair sigma H x z = a ∧ hermitianPair sigma H u z = b := by
  let f := (pairRightLinear sigma H x).comp Z.subtype
  let g := (pairRightLinear sigma H u).comp Z.subtype
  have hx0 : x ≠ 0 := hli.ne_zero 0
  have hf : f ≠ 0 := by
    intro he
    apply hx0
    apply hND x hx
    intro z hz
    exact LinearMap.congr_fun he ⟨z,hz⟩
  have hg : ∀ c : K, g ≠ c • f := by
    intro c he
    have hmem : u - sigma.symm c • x ∈ P := P.sub_mem hu (P.smul_mem _ hx)
    have hz : u - sigma.symm c • x = 0 := hND _ hmem (by
      intro z hz
      have hh := LinearMap.congr_fun he ⟨z,hz⟩
      change hermitianPair sigma H u z = c * hermitianPair sigma H x z at hh
      have ha := hermitianPair_add_left sigma H (u-sigma.symm c • x) (sigma.symm c • x) z
      have hs := hermitianPair_smul sigma H (sigma.symm c) 1 x z
      simp only [one_smul,sigma.apply_symm_apply,mul_one] at hs
      rw [sub_add_cancel,hs,hh] at ha
      exact add_right_cancel (ha.symm.trans (zero_add (c * hermitianPair sigma H x z)).symm))
    exact (LinearIndependent.pair_iff' hx0).mp hli (sigma.symm c) (sub_eq_zero.mp hz).symm
  obtain ⟨z,hz,hz'⟩ := CFSGTwoFunctionalPrescription.exists_pair_values f g hf hg a b
  exact ⟨z.val,z.property,hz,hz'⟩

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
