import SymmetricSubgroupAsymptotics.CFSGHermitianMixedTest
import SymmetricSubgroupAsymptotics.CFSGHermitianFixedProjection

/-! In any space spanned by opposed singular spaces of rank at
least two, fixing their points and every strong mixed ray fixes ALL
singular points. The test is constructed without a rank-two restriction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

private theorem sum_nonzero (P Z : Submodule K (I → K)) (hdis : Disjoint P Z)
    (u z : I → K) (hu : u ∈ P) (hz : z ∈ Z) (hu0 : u ≠ 0) : u + z ≠ 0 := by
  intro h
  have huZ : u ∈ Z := by
    rw [add_eq_zero_iff_eq_neg.mp h]
    exact Z.neg_mem hz
  exact hu0 ((Submodule.disjoint_def.mp hdis) u hu huZ)

theorem hermitian_even_fixes_all
    (hswap : ∀ v w, hermitianPair sigma H v w = 0 ↔ hermitianPair sigma H w v = 0)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (hdP : 2 ≤ Module.finrank K P.val) (hdis : Disjoint P.val Z.val) (htop : P.val ⊔ Z.val = ⊤)
    (hNDp : ∀ x ∈ P.val, (∀ y ∈ Z.val, hermitianPair sigma H x y = 0) → x = 0)
    (hNDz : ∀ y ∈ Z.val, (∀ x ∈ P.val, hermitianPair sigma H y x = 0) → y = 0)
    (hfixP : ∀ R : SingularPoint sigma H, R.val ≤ P.val → f R = R)
    (hfixZ : ∀ R : SingularPoint sigma H, R.val ≤ Z.val → f R = R)
    (hfixMixed : ∀ (x y : I → K), x ∈ P.val → x ≠ 0 → y ∈ Z.val → y ≠ 0 →
      hermitianPair sigma H y x = 0 → ∀ R : SingularPoint sigma H,
      R.val = K ∙ (x + y) → f R = R) :
    ∀ R : SingularPoint sigma H, f R = R := by
  intro R
  obtain ⟨v, hvR, hv0⟩ := singularPoint_nonzero sigma H R
  have hvTop : v ∈ P.val ⊔ Z.val := by rw [htop]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hvTop
  have hRmem : x + y ∈ R.val := hxy.symm ▸ hvR
  have hsum0 : x + y ≠ 0 := hxy.symm ▸ hv0
  have hRspan := singularPoint_span sigma H R (x + y) hRmem hsum0
  by_cases hx0 : x = 0
  · apply hfixZ R
    rw [hRspan]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    simpa only [hx0, zero_add] using hy
  by_cases hy0 : y = 0
  · apply hfixP R
    rw [hRspan]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    simpa only [hy0, add_zero] using hx
  by_cases hyx : hermitianPair sigma H y x = 0
  · exact hfixMixed x y hx hx0 hy hy0 hyx R hRspan
  obtain ⟨v', hv', hv'0⟩ := singularPoint_nonzero sigma H (f R)
  have hv'Top : v' ∈ P.val ⊔ Z.val := by rw [htop]; trivial
  obtain ⟨x', hx', y', hy', hxy'⟩ := Submodule.mem_sup.mp hv'Top
  have hR'mem : x' + y' ∈ (f R).val := hxy'.symm ▸ hv'
  have hsum'0 : x' + y' ≠ 0 := hxy'.symm ▸ hv'0
  obtain ⟨a, ha, hax⟩ := hermitian_fixed_projection_proportional sigma H f hf P Z hNDp hfixZ R
    x y x' y' hx hy hx' hy' hx0 hRmem hsum0 hR'mem hsum'0
  obtain ⟨b, _, hby⟩ := hermitian_fixed_projection_proportional sigma H f hf Z P hNDz hfixP R
    y x y' x' hy hx hy' hx' hy0
    (by simpa only [add_comm] using hRmem) (by simpa only [add_comm] using hsum0)
    (by simpa only [add_comm] using hR'mem) (by simpa only [add_comm] using hsum'0)
  have himage : a • x + b • y ∈ (f R).val := by rwa [hax, hby] at hR'mem
  have himage0 : a • x + b • y ≠ 0 := by rwa [hax, hby] at hsum'0
  obtain ⟨u, hu, z, hz, hu0, hz0, hzu, hyu, hxz⟩ :=
    exists_hermitian_mixed_test sigma H hswap P.val Z.val hdP hNDp x y hx hx0 hyx
  have hq0 : u + z ≠ 0 := sum_nonzero P.val Z.val hdis u z hu hz hu0
  have huz := (hswap z u).mp hzu
  have hqnorm : hermitianPair sigma H (u + z) (u + z) = 0 := by
    rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
      P.property u hu u hu, Z.property z hz z hz, hzu, huz]
    simp only [zero_add]
  let Q := singularRay sigma H (u + z) hq0 hqnorm
  have hQfix : f Q = Q := hfixMixed u z hu hu0 hz hz0 hzu Q rfl
  have hxq : hermitianPair sigma H x (u + z) = -hermitianPair sigma H y u := by
    rw [hermitianPair_add_right, P.property x hx u hu, hxz, zero_add]
  have hyq : hermitianPair sigma H y (u + z) = hermitianPair sigma H y u := by
    rw [hermitianPair_add_right, Z.property y hy z hz, add_zero]
  have hRorthQ : Orthogonal sigma H R.val Q.val := by
    apply (orthogonal_iff_singular_representatives sigma H R Q (x + y) (u + z)
      hRmem (Submodule.mem_span_singleton_self _) hsum0 hq0).mpr
    rw [hermitianPair_add_left, hxq, hyq, neg_add_cancel]
  have himageOrth := (hf R Q).mpr hRorthQ
  rw [hQfix] at himageOrth
  have he := himageOrth (a • x + b • y) himage (u + z) (Submodule.mem_span_singleton_self _)
  rw [hermitianPair_add_left] at he
  have hsa := hermitianPair_smul sigma H a 1 x (u + z)
  have hsb := hermitianPair_smul sigma H b 1 y (u + z)
  simp only [one_smul, mul_one, hxq, hyq] at hsa hsb
  rw [hsa, hsb] at he
  have heq : sigma a * hermitianPair sigma H y u = sigma b * hermitianPair sigma H y u := by
    calc
      _ = sigma b * hermitianPair sigma H y u -
          (sigma a * (-hermitianPair sigma H y u) + sigma b * hermitianPair sigma H y u) := by ring
      _ = _ := by rw [he, sub_zero]
  have hab : a = b := sigma.injective (mul_right_cancel₀ hyu heq)
  apply Subtype.ext
  calc
    (f R).val = K ∙ (a • x + b • y) := singularPoint_span sigma H (f R) _ himage himage0
    _ = K ∙ (a • (x + y)) := by rw [← hab, smul_add]
    _ = K ∙ (x + y) := Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) _
    _ = R.val := hRspan.symm

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
