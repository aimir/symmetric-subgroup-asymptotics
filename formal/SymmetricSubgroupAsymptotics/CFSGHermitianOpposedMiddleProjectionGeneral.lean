import SymmetricSubgroupAsymptotics.CFSGHermitianMixedComponentComparison

/-! Fixed opposed point planes and their orthogonal mixed rays determine
ONE common multiplier on the two opposed components of an outside point.
The perpendicular remainder is retained, rather than assumed singular. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

private theorem pair_add_smul_zero (sigma : K ≃+* K) (H : Matrix I I K)
    (x h w : I → K) (t : K) (hx : hermitianPair sigma H x w = 0)
    (hh : hermitianPair sigma H h w = 0) : hermitianPair sigma H (x + t • h) w = 0 := by
  have hs := hermitianPair_smul sigma H t 1 h w
  simp only [one_smul, mul_one, hh, mul_zero] at hs
  rw [hermitianPair_add_left, hx, hs, zero_add]

theorem hermitian_opposed_middle_projection_of_two_le (sigma : K ≃+* K) (H : Matrix I I K)
    (hswap : ∀ v w, hermitianPair sigma H v w = 0 ↔ hermitianPair sigma H w v = 0)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (hdP : 2 ≤ Module.finrank K P.val) (hdis : Disjoint P.val Z.val)
    (hNDp : ∀ x ∈ P.val, (∀ y ∈ Z.val, hermitianPair sigma H x y = 0) → x = 0)
    (hNDz : ∀ y ∈ Z.val, (∀ x ∈ P.val, hermitianPair sigma H y x = 0) → y = 0)
    (hfixP : ∀ Q : SingularPoint sigma H, Q.val ≤ P.val → f Q = Q)
    (hfixZ : ∀ Q : SingularPoint sigma H, Q.val ≤ Z.val → f Q = Q)
    (hfixMixed : ∀ (u z : I → K), u ∈ P.val → u ≠ 0 → z ∈ Z.val → z ≠ 0 →
      hermitianPair sigma H z u = 0 → ∀ Q : SingularPoint sigma H,
      Q.val = K ∙ (u + z) → f Q = Q)
    (h : I → K) (hh : ∀ w ∈ P.val ⊔ Z.val, hermitianPair sigma H h w = 0)
    (R : SingularPoint sigma H) (x y x' y' : I → K) (t t' : K)
    (hx : x ∈ P.val) (hy : y ∈ Z.val) (hx' : x' ∈ P.val) (hy' : y' ∈ Z.val)
    (hWnorm : hermitianPair sigma H (x + y) (x + y) ≠ 0)
    (hR : x + y + t • h ∈ R.val) (hR0 : x + y + t • h ≠ 0)
    (himage : x' + y' + t' • h ∈ (f R).val) (himage0 : x' + y' + t' • h ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ x' = a • x ∧ y' = a • y := by
  have hx0 : x ≠ 0 := by
    intro hxz
    exact hWnorm (by simpa only [hxz, zero_add] using Z.property y hy y hy)
  have hy0 : y ≠ 0 := by
    intro hyz
    exact hWnorm (by simpa only [hyz, add_zero] using P.property x hx x hx)
  have hyx : hermitianPair sigma H y x ≠ 0 := by
    intro hyx
    have hxy := (hswap y x).mp hyx
    apply hWnorm
    rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
      P.property x hx x hx, Z.property y hy y hy, hxy, hyx]
    simp only [zero_add]
  have hzrest (z : I → K) (hz : z ∈ Z.val) : hermitianPair sigma H (y + t • h) z = 0 :=
    pair_add_smul_zero sigma H y h z t (Z.property y hy z hz) (hh z ((show Z.val ≤ P.val ⊔ Z.val from le_sup_right) hz))
  have hzrest' (z : I → K) (hz : z ∈ Z.val) : hermitianPair sigma H (y' + t' • h) z = 0 :=
    pair_add_smul_zero sigma H y' h z t' (Z.property y' hy' z hz) (hh z ((show Z.val ≤ P.val ⊔ Z.val from le_sup_right) hz))
  obtain ⟨a,ha,hax⟩ := hermitian_fixed_projection_with_remainder sigma H f hf P.val Z hNDp hfixZ R
    x (y + t • h) x' (y' + t' • h) hx hx' hzrest hzrest' hx0
    (by simpa only [add_assoc] using hR) (by simpa only [add_assoc] using hR0)
    (by simpa only [add_assoc] using himage) (by simpa only [add_assoc] using himage0)
  have hprest (p : I → K) (hp : p ∈ P.val) : hermitianPair sigma H (x + t • h) p = 0 :=
    pair_add_smul_zero sigma H x h p t (P.property x hx p hp) (hh p ((show P.val ≤ P.val ⊔ Z.val from le_sup_left) hp))
  have hprest' (p : I → K) (hp : p ∈ P.val) : hermitianPair sigma H (x' + t' • h) p = 0 :=
    pair_add_smul_zero sigma H x' h p t' (P.property x' hx' p hp) (hh p ((show P.val ≤ P.val ⊔ Z.val from le_sup_left) hp))
  obtain ⟨b,hb,hby⟩ := hermitian_fixed_projection_with_remainder sigma H f hf Z.val P hNDz hfixP R
    y (x + t • h) y' (x' + t' • h) hy hy' hprest hprest' hy0
    (by simpa only [add_assoc, add_comm, add_left_comm] using hR)
    (by simpa only [add_assoc, add_comm, add_left_comm] using hR0)
    (by simpa only [add_assoc, add_comm, add_left_comm] using himage)
    (by simpa only [add_assoc, add_comm, add_left_comm] using himage0)
  have hm (w : I → K) (hw : w ∈ P.val ⊔ Z.val) : hermitianPair sigma H (t • h) w = 0 := by
    have hs := hermitianPair_smul sigma H t 1 h w
    simpa only [one_smul, mul_one, hh w hw, mul_zero] using hs
  have hm' (w : I → K) (hw : w ∈ P.val ⊔ Z.val) : hermitianPair sigma H (t' • h) w = 0 := by
    have hs := hermitianPair_smul sigma H t' 1 h w
    simpa only [one_smul, mul_one, hh w hw, mul_zero] using hs
  have hab := hermitian_mixed_component_scalars_eq_of_two_le sigma H hswap f hf P Z hdP hdis hNDp
    hfixMixed R x y (t • h) (t' • h) a b hx hy hx0 hyx hm hm' hR hR0
    (by rwa [hax,hby] at himage)
  exact ⟨a,ha,hax,by simpa only [hab] using hby⟩

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
