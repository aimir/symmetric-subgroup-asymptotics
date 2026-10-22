import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointMiddleDichotomy
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleSliceConnected

/-! The actual orthogonality-permutation kernel fixing all zero-middle
singular points has at most two elements. The two possibilities are
identity and the literal paired-minus/middle-fixed isometry. The sign
is forced globally by the actual three-edge slice connectivity, also
in F3; no common-neighbour assertion for antipodes is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleKernel
open CFSGOrthogonalBSerreMatrices CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
open CFSGOrthogonalBZeroMiddleScalarCoupling CFSGOrthogonalBPointMiddleDichotomy
open CFSGOrthogonalBMiddleSliceConnected CFSGOrthogonalBNonzeroMiddleCommonNeighbour
open CFSGOrthogonalBParabolicColumn CFSGOrthogonalBIntrinsicLongRoots
variable (K : Type) [Field K] [Finite K]

def slicePoint (s : ℕ) (v : Slice K s) : Points (Form K s) :=
  ray (Form K s) v.val (ne_zero_of_middle_one K _ v.val v.property.2) v.property.1

theorem slice_mem (s : ℕ) (v : Slice K s) : v.val ∈ (slicePoint K s v).val :=
  Submodule.subset_span (by simp)

theorem zeroOn_slices_iff (s : ℕ) (v w : Slice K s) :
    ZeroOn (Form K s) (slicePoint K s v).val (slicePoint K s w).val ↔
      (Form K s) v.val w.val = 0 := by
  constructor
  · intro h
    exact h _ (slice_mem K s v) _ (slice_mem K s w)
  · intro h x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [map_smul, LinearMap.smul_apply, h, smul_zero]

theorem point_zero_middle_or_slice (s : ℕ) (P : Points (Form K s)) :
    (∀ z ∈ P.val, z (middle (s + 3)) = 0) ∨
      ∃ v : Slice K s, slicePoint K s v = P := by
  obtain ⟨x, hx, hx0⟩ := point_nonzero (Form K s) P
  by_cases hm : x (middle (s + 3)) = 0
  · left
    intro z hz
    rw [← point_span (Form K s) P x hx hx0] at hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp only [Pi.smul_apply, smul_eq_mul, hm, mul_zero]
  · right
    let y := (x (middle (s + 3)))⁻¹ • x
    have hy : y ∈ P.val := P.val.smul_mem _ hx
    have hym : y (middle (s + 3)) = 1 := inv_mul_cancel₀ hm
    let v : Slice K s := ⟨y, P.property.2 y hy y hy, hym⟩
    refine ⟨v, point_eq_of_common_nonzero (Form K s) _ P y (slice_mem K s v) hy ?_⟩
    exact ne_zero_of_middle_one K _ y hym

theorem mixed_pairing (s : ℕ) (v w : Slice K s)
    (hvw : (Form K s) v.val w.val = 0) :
    (Form K s) v.val (CFSGOrthogonalBMiddleFlip.vectorEquiv K (s + 3) w.val) = 2 := by
  rw [CFSGOrthogonalBMiddleFlip.eq_antipode K _ w.val w.property.2]
  unfold antipode
  rw [map_sub, map_smul, smul_eq_mul, pairing_middle K (s + 3) v.val,
    v.property.2, hvw, mul_one, sub_zero]

theorem edge_fix_imp (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (Form K s) ≃ Points (Form K s))
    (horth : ∀ P Q, ZeroOn (Form K s) (f P).val (f Q).val ↔ ZeroOn (Form K s) P.val Q.val)
    (hfix : ∀ R : Points (Form K s), (∀ z ∈ R.val, z (middle (s + 3)) = 0) → f R = R)
    (v w : Slice K s) (hvw : (Form K s) v.val w.val = 0)
    (hv : f (slicePoint K s v) = slicePoint K s v) :
    f (slicePoint K s w) = slicePoint K s w := by
  by_contra hw
  have hwflip : f (slicePoint K s w) =
      CFSGOrthogonalBMiddleFlip.pointEquiv K (s + 3) (slicePoint K s w) :=
    (point_eq_or_flip K h2 s f horth hfix (slicePoint K s w) w.val
      (slice_mem K s w) w.property.2).resolve_left hw
  have hz := (horth (slicePoint K s v) (slicePoint K s w)).mpr
    ((zeroOn_slices_iff K s v w).mpr hvw)
  have hvm : v.val ∈ (f (slicePoint K s v)).val := by rw [hv]; exact slice_mem K s v
  have hwm : CFSGOrthogonalBMiddleFlip.vectorEquiv K (s + 3) w.val ∈
      (f (slicePoint K s w)).val := by
    rw [hwflip]
    exact CFSGOrthogonalBMiddleFlip.image_mem K _ _ w.val (slice_mem K s w)
  exact h2 ((mixed_pairing K s v w hvw).symm.trans (hz _ hvm _ hwm))

theorem fixed_status_constant (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (Form K s) ≃ Points (Form K s))
    (horth : ∀ P Q, ZeroOn (Form K s) (f P).val (f Q).val ↔ ZeroOn (Form K s) P.val Q.val)
    (hfix : ∀ R : Points (Form K s), (∀ z ∈ R.val, z (middle (s + 3)) = 0) → f R = R)
    (v w : Slice K s) :
    (f (slicePoint K s v) = slicePoint K s v) ↔
      (f (slicePoint K s w) = slicePoint K s w) := by
  apply Iff.of_eq
  apply constant_of_orthogonal_edges K h2 s
    (fun u => f (slicePoint K s u) = slicePoint K s u) _ v w
  intro u t hut
  apply propext
  constructor
  · exact edge_fix_imp K h2 s f horth hfix u t hut
  · have htu : (Form K s) t.val u.val = 0 :=
      (gram_pairing_symmetric (s + 3) t.val u.val).trans hut
    exact edge_fix_imp K h2 s f horth hfix t u htu

theorem eq_identity_or_middle_flip (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (Form K s) ≃ Points (Form K s))
    (horth : ∀ P Q, ZeroOn (Form K s) (f P).val (f Q).val ↔ ZeroOn (Form K s) P.val Q.val)
    (hfix : ∀ R : Points (Form K s), (∀ z ∈ R.val, z (middle (s + 3)) = 0) → f R = R) :
    f = Equiv.refl _ ∨ f = CFSGOrthogonalBMiddleFlip.pointEquiv K (s + 3) := by
  classical
  by_cases hall : ∀ v : Slice K s, f (slicePoint K s v) = slicePoint K s v
  · left
    apply Equiv.ext
    intro P
    change f P = P
    rcases point_zero_middle_or_slice K s P with hm | ⟨v, rfl⟩
    · exact hfix P hm
    · exact hall v
  · right
    obtain ⟨v, hv⟩ := not_forall.mp hall
    apply Equiv.ext
    intro P
    rcases point_zero_middle_or_slice K s P with hm | ⟨w, rfl⟩
    · exact (hfix P hm).trans (CFSGOrthogonalBMiddleFlip.fixes_zero_middle K _ P hm).symm
    · have hw : f (slicePoint K s w) ≠ slicePoint K s w :=
        fun hh => hv ((fixed_status_constant K h2 s f horth hfix v w).mpr hh)
      exact (point_eq_or_flip K h2 s f horth hfix (slicePoint K s w) w.val
        (slice_mem K s w) w.property.2).resolve_left hw

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleKernel
