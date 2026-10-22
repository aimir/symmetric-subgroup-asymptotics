import SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleScalarCoupling
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleNormDichotomy
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleFlip

/-! The actual image point, with its own original representative,
normalizes to exactly the original vector or its paired antipode.
No image-recognition hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointMiddleDichotomy
open CFSGOrthogonalBSerreMatrices CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
open CFSGOrthogonalBZeroMiddleScalarCoupling CFSGOrthogonalBMiddleNormDichotomy
open CFSGOrthogonalBNonzeroMiddleCommonNeighbour
variable (K : Type) [Field K] [Finite K]

theorem ne_zero_of_middle_one (n : ℕ) (v : Index n → K) (hm : v (middle n) = 1) : v ≠ 0 := by
  intro hz
  have hh := congrFun hz (middle n)
  change v (middle n) = 0 at hh
  exact one_ne_zero (hm.symm.trans hh)

theorem image_middle_ne_zero (s : ℕ)
    (f : Points (Form K s) ≃ Points (Form K s))
    (hfix : ∀ R : Points (Form K s), (∀ z ∈ R.val, z (middle (s + 3)) = 0) → f R = R)
    (P : Points (Form K s)) (v x : Index (s + 3) → K)
    (hv : v ∈ P.val) (hvm : v (middle (s + 3)) = 1)
    (hx : x ∈ (f P).val) (hx0 : x ≠ 0) : x (middle (s + 3)) ≠ 0 := by
  intro hxm
  have hm (z : Index (s + 3) → K) (hz : z ∈ (f P).val) : z (middle (s + 3)) = 0 := by
    rw [← point_span (Form K s) (f P) x hx hx0] at hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp only [Pi.smul_apply, smul_eq_mul, hxm, mul_zero]
  have hfp : f P = P := f.injective (hfix (f P) hm)
  have hz := hm v (by rw [hfp]; exact hv)
  exact one_ne_zero (hvm.symm.trans hz)

theorem exists_normalized_image (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (Form K s) ≃ Points (Form K s))
    (horth : ∀ P Q, ZeroOn (Form K s) (f P).val (f Q).val ↔ ZeroOn (Form K s) P.val Q.val)
    (hfix : ∀ R : Points (Form K s), (∀ z ∈ R.val, z (middle (s + 3)) = 0) → f R = R)
    (P : Points (Form K s)) (v : Index (s + 3) → K)
    (hv : v ∈ P.val) (hvm : v (middle (s + 3)) = 1) :
    ∃ y : Index (s + 3) → K, y ∈ (f P).val ∧
      (Form K s) y y = 0 ∧ y (middle (s + 3)) = 1 ∧
      (y = v ∨ y = antipode K (s + 3) v) := by
  obtain ⟨x, hx, hx0⟩ := point_nonzero (Form K s) (f P)
  have hxm := image_middle_ne_zero K s f hfix P v x hv hvm hx hx0
  let y := (x (middle (s + 3)))⁻¹ • x
  have hy : y ∈ (f P).val := (f P).val.smul_mem _ hx
  have hym : y (middle (s + 3)) = 1 := inv_mul_cancel₀ hxm
  have hv0 := ne_zero_of_middle_one K (s + 3) v hvm
  have hy0 := ne_zero_of_middle_one K (s + 3) y hym
  have hvn : (Form K s) v v = 0 := P.property.2 v hv v hv
  have hyn : (Form K s) y y = 0 := (f P).property.2 y hy y hy
  obtain ⟨c, _, hp, hn⟩ := paired_projections_common_scalar K h2 s f horth hfix
    P v y hv hy hv0 hy0 (projections_ne_zero K _ v hvn hvm).1
      (projections_ne_zero K _ v hvn hvm).2
  exact ⟨y, hy, hyn, hym, eq_or_antipode_of_paired_scalar K _ v y hvn hyn hvm hym c hp hn⟩

theorem point_eq_or_flip (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (Form K s) ≃ Points (Form K s))
    (horth : ∀ P Q, ZeroOn (Form K s) (f P).val (f Q).val ↔ ZeroOn (Form K s) P.val Q.val)
    (hfix : ∀ R : Points (Form K s), (∀ z ∈ R.val, z (middle (s + 3)) = 0) → f R = R)
    (P : Points (Form K s)) (v : Index (s + 3) → K)
    (hv : v ∈ P.val) (hvm : v (middle (s + 3)) = 1) :
    f P = P ∨ f P = CFSGOrthogonalBMiddleFlip.pointEquiv K (s + 3) P := by
  obtain ⟨y, hy, _, hym, he | he⟩ := exists_normalized_image K h2 s f horth hfix P v hv hvm
  · left
    apply point_eq_of_common_nonzero (Form K s) _ P y hy
    · rw [he]; exact hv
    · exact ne_zero_of_middle_one K _ y hym
  · right
    apply point_eq_of_common_nonzero (Form K s) _ _ y hy
    · rw [he, ← CFSGOrthogonalBMiddleFlip.eq_antipode K _ v hvm]
      exact CFSGOrthogonalBMiddleFlip.image_mem K _ P v hv
    · exact ne_zero_of_middle_one K _ y hym

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointMiddleDichotomy
