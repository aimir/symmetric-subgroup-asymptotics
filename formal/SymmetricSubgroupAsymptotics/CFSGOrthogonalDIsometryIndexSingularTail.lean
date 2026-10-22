import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailLinearExtension
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane

/-! A SAME-Q singular subspace containing the first singular axis
has an actual split-D tail of dimension one less. The kernel is the
literal first line. Quadratic zero, rather than polar-zero alone, is
retained everywhere, so the result includes characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexSingularTail
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGOrthogonalDIndexQuadraticNeighborPlane
variable (K : Type) [Field K]

theorem first_nonzero (n : ℕ) :
    (Pi.single (Sum.inl (0 : Fin (n + 1))) 1 : Index (n + 1) → K) ≠ 0 := by
  intro h
  have he := congrFun h (Sum.inl (0 : Fin (n + 1)))
  exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using he)

theorem tail_first_zero (n : ℕ) :
    tailRestrictionLinear K n (Pi.single (Sum.inl (0 : Fin (n + 1))) 1) = 0 := by
  funext i
  rcases i with i | i <;> simp [tailRestrictionLinear, tailRestriction, tailIndex]

theorem negative_head_zero (n : ℕ) (P : Subspaces (splitQuadraticForm K (n + 1)))
    (hu : Pi.single (Sum.inl (0 : Fin (n + 1))) 1 ∈ P.val)
    (v : Index (n + 1) → K) (hv : v ∈ P.val) : v (Sum.inr 0) = 0 := by
  have he := polar_zero_of_singular (splitQuadraticForm K (n + 1)) P.val P.property
    (Pi.single (Sum.inl (0 : Fin (n + 1))) 1) v hu hv
  rw [splitQuadraticForm_polar, pairing_first_positive] at he
  exact he

def tailSubspace (n : ℕ) (P : Subspaces (splitQuadraticForm K (n + 1)))
    (hu : Pi.single (Sum.inl (0 : Fin (n + 1))) 1 ∈ P.val) :
    Subspaces (splitQuadraticForm K n) :=
  ⟨P.val.map (tailRestrictionLinear K n), by
    rintro x ⟨v, hv, rfl⟩
    rw [splitQuadraticForm_apply]
    have he := P.property v hv
    rw [splitQuadraticForm_apply] at he
    exact (splitQ_tail_of_negative_head_zero K n v
      (negative_head_zero K n P hu v hv)).symm.trans he⟩

theorem tailSubspace_finrank (n : ℕ) (P : Subspaces (splitQuadraticForm K (n + 1)))
    (hu : Pi.single (Sum.inl (0 : Fin (n + 1))) 1 ∈ P.val) :
    Module.finrank K (tailSubspace K n P hu).val + 1 = Module.finrank K P.val := by
  let u : Index (n + 1) → K := Pi.single (Sum.inl 0) 1
  let f := (tailRestrictionLinear K n).comp P.val.subtype
  have hk : f.ker.map P.val.subtype = Submodule.span K {u} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      have ht : tailRestriction K n x.val = 0 := hx
      have he := vector_eq_first_of_tail_zero K n x.val ht
        (negative_head_zero K n P hu x.val x.property)
      exact Submodule.mem_span_singleton.mpr ⟨x.val (Sum.inl 0), he.symm⟩
    · intro hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      refine ⟨⟨c • u, P.val.smul_mem c hu⟩, ?_, rfl⟩
      change tailRestrictionLinear K n (c • u) = 0
      rw [map_smul, tail_first_zero, smul_zero]
  have hker : Module.finrank K f.ker = 1 :=
    (Submodule.finrank_map_subtype_eq P.val f.ker).symm.trans
      ((congrArg (fun T : Submodule K (Index (n + 1) → K) => Module.finrank K T) hk).trans
        (finrank_span_singleton (first_nonzero K n)))
  have hr : f.range = P.val.map (tailRestrictionLinear K n) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hd := f.finrank_range_add_finrank_ker
  rw [hr, hker] at hd
  exact hd

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexSingularTail
