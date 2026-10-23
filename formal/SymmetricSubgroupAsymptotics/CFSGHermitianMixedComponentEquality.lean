import SymmetricSubgroupAsymptotics.CFSGHermitianPlaneMixedTest
import SymmetricSubgroupAsymptotics.CFSGHermitianFixedProjectionRemainder

/-! Orthogonal mixed rays force the two opposed component scalars to
agree even in the presence of an anisotropic perpendicular remainder.
The separating mixed test is constructed on the actual singular planes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem hermitian_mixed_component_scalars_eq (sigma : K ≃+* K) (H : Matrix I I K)
    (hswap : ∀ v w, hermitianPair sigma H v w = 0 ↔ hermitianPair sigma H w v = 0)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (hdP : Module.finrank K P.val = 2)
    (hdZ : Module.finrank K Z.val = 2) (hdis : Disjoint P.val Z.val)
    (hNDz : ∀ y ∈ Z.val, (∀ x ∈ P.val, hermitianPair sigma H y x = 0) → y = 0)
    (hfixMixed : ∀ (u z : I → K), u ∈ P.val → u ≠ 0 → z ∈ Z.val → z ≠ 0 →
      hermitianPair sigma H z u = 0 → ∀ Q : SingularPoint sigma H,
      Q.val = K ∙ (u + z) → f Q = Q)
    (R : SingularPoint sigma H) (x y m m' : I → K) (a b : K)
    (hx : x ∈ P.val) (hy : y ∈ Z.val) (hx0 : x ≠ 0)
    (hyx : hermitianPair sigma H y x ≠ 0)
    (hm : ∀ w ∈ P.val ⊔ Z.val, hermitianPair sigma H m w = 0)
    (hm' : ∀ w ∈ P.val ⊔ Z.val, hermitianPair sigma H m' w = 0)
    (hR : x + y + m ∈ R.val) (hR0 : x + y + m ≠ 0)
    (himage : a • x + b • y + m' ∈ (f R).val) : a = b := by
  obtain ⟨u,hu,z,hz,hu0,hz0,hzu,hyu,hxz⟩ :=
    exists_hermitian_plane_mixed_test sigma H hswap P.val Z.val hdP hdZ hNDz x y hx hx0 hyx
  have hq0 : u + z ≠ 0 := by
    intro h
    have huZ : u ∈ Z.val := by
      rw [add_eq_zero_iff_eq_neg.mp h]
      exact Z.val.neg_mem hz
    exact hu0 ((Submodule.disjoint_def.mp hdis) u hu huZ)
  have huz := (hswap z u).mp hzu
  have hqnorm : hermitianPair sigma H (u + z) (u + z) = 0 := by
    rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
      P.property u hu u hu, Z.property z hz z hz, hzu, huz]
    simp only [zero_add]
  let Q := singularRay sigma H (u + z) hq0 hqnorm
  have hQfix : f Q = Q := hfixMixed u z hu hu0 hz hz0 hzu Q rfl
  have hqW : u + z ∈ P.val ⊔ Z.val := Submodule.add_mem_sup hu hz
  have hxq : hermitianPair sigma H x (u + z) = -hermitianPair sigma H y u := by
    rw [hermitianPair_add_right, P.property x hx u hu, hxz, zero_add]
  have hyq : hermitianPair sigma H y (u + z) = hermitianPair sigma H y u := by
    rw [hermitianPair_add_right, Z.property y hy z hz, add_zero]
  have hRQ : Orthogonal sigma H R.val Q.val := by
    apply (orthogonal_iff_singular_representatives sigma H R Q (x + y + m) (u + z)
      hR (Submodule.mem_span_singleton_self _) hR0 hq0).mpr
    rw [hermitianPair_add_left, hermitianPair_add_left, hxq, hyq, hm _ hqW, neg_add_cancel, add_zero]
  have hIQ := (hf R Q).mpr hRQ
  rw [hQfix] at hIQ
  have he := hIQ (a • x + b • y + m') himage (u + z) (Submodule.mem_span_singleton_self _)
  rw [hermitianPair_add_left, hermitianPair_add_left, hm' _ hqW, add_zero] at he
  have hsa := hermitianPair_smul sigma H a 1 x (u + z)
  have hsb := hermitianPair_smul sigma H b 1 y (u + z)
  simp only [one_smul, mul_one, hxq, hyq] at hsa hsb
  rw [hsa, hsb] at he
  have heq : sigma a * hermitianPair sigma H y u = sigma b * hermitianPair sigma H y u := by
    calc
      _ = sigma b * hermitianPair sigma H y u -
          (sigma a * (-hermitianPair sigma H y u) + sigma b * hermitianPair sigma H y u) := by ring
      _ = _ := by rw [he, sub_zero]
  exact sigma.injective (mul_right_cancel₀ hyu heq)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
