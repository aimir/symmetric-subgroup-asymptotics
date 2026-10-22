import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceEquivalence

/-! Actual Q-singular point/plane incidence preserves projective joins
inside every original Q-singular subspace, including characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem point_le_iff_eq (Q : QuadraticForm K V) (P R : Points Q) : P.val ≤ R.val ↔ P = R := by
  constructor
  · intro h
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_le h (by rw [P.property.1, R.property.1]))
  · rintro rfl
    exact le_rfl

variable (Q : QuadraticForm K V) (f : Points Q ≃ Points Q) (l : Planes Q ≃ Planes Q)
    (hinc : ∀ P L, (f P).val ≤ (l L).val ↔ P.val ≤ L.val)

include l hinc in
theorem preserves_point_join_incidence (W : Subspaces Q) (P R Z : Points Q)
    (hP : P.val ≤ W.val) (hR : R.val ≤ W.val) :
    (f Z).val ≤ (f P).val ⊔ (f R).val ↔ Z.val ≤ P.val ⊔ R.val := by
  by_cases he : P = R
  · subst R
    simp only [sup_idem, point_le_iff_eq, f.injective.eq_iff]
  let L := joinPlane Q W P R hP hR he
  have hfp := (point_le_image_iff Q f l hinc W P).mpr hP
  have hfr := (point_le_image_iff Q f l hinc W R).mpr hR
  let L' := joinPlane Q (imageSubspace Q f l hinc W) (f P) (f R) hfp hfr
    (fun h => he (f.injective h))
  have hd : Module.finrank K ↥((f P).val ⊔ (f R).val) = 2 := L'.property.1
  have hle : (f P).val ⊔ (f R).val ≤ (l L).val :=
    sup_le ((hinc P L).mpr le_sup_left) ((hinc R L).mpr le_sup_right)
  have heq : (f P).val ⊔ (f R).val = (l L).val := Submodule.eq_of_le_of_finrank_le hle
    (by rw [(l L).property.1, hd])
  rw [heq]
  exact hinc Z L

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
