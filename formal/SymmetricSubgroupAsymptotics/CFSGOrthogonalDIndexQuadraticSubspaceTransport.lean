import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints

/-! Compatible literal point/plane bijections transport every Q-zero
submodule. Addition uses an ACTUAL image singular plane. Every resulting
vector lies on an original Q-zero image ray, retaining Q also in char2. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V) (f : Points Q ≃ Points Q) (l : Planes Q ≃ Planes Q)
    (hinc : ∀ P L, (f P).val ≤ (l L).val ↔ P.val ≤ L.val)

def imageSubmodule (W : Subspaces Q) : Submodule K V where
  carrier := {v | v = 0 ∨ ∃ P : Points Q, P.val ≤ W.val ∧ v ∈ (f P).val}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (rfl | ⟨P, hP, hx⟩) (rfl | ⟨R, hR, hy⟩)
    · exact Or.inl (zero_add 0)
    · exact Or.inr ⟨R, hR, by simpa only [zero_add] using hy⟩
    · exact Or.inr ⟨P, hP, by simpa only [add_zero] using hx⟩
    by_cases hz : x + y = 0
    · exact Or.inl hz
    by_cases he : P = R
    · subst R
      exact Or.inr ⟨P, hP, (f P).val.add_mem hx hy⟩
    let L := joinPlane Q W P R hP hR he
    have hpL : P.val ≤ L.val := le_sup_left
    have hrL : R.val ≤ L.val := le_sup_right
    have hxy : x + y ∈ (l L).val := (l L).val.add_mem ((hinc P L).mpr hpL hx)
      ((hinc R L).mpr hrL hy)
    let S := ray Q (x + y) hz ((l L).property.2 (x + y) hxy)
    have hs : S.val ≤ (l L).val := (Submodule.span_singleton_le_iff_mem _ _).mpr hxy
    have hi : (f.symm S).val ≤ L.val := (hinc (f.symm S) L).mp (by
      simpa only [f.apply_symm_apply] using hs)
    refine Or.inr ⟨f.symm S, hi.trans (sup_le hP hR), ?_⟩
    rw [f.apply_symm_apply]
    exact Submodule.subset_span (by simp)
  smul_mem' := by
    intro a v hv
    rcases hv with rfl | ⟨P, hP, hv⟩
    · exact Or.inl (smul_zero a)
    · exact Or.inr ⟨P, hP, (f P).val.smul_mem a hv⟩

theorem point_le_image_iff (W : Subspaces Q) (P : Points Q) :
    (f P).val ≤ imageSubmodule Q f l hinc W ↔ P.val ≤ W.val := by
  constructor
  · intro h
    obtain ⟨v, hv, hv0⟩ := point_nonzero Q (f P)
    rcases h hv with hz | ⟨R, hR, hvR⟩
    · exact False.elim (hv0 hz)
    · have he := f.injective (point_eq_of_common_nonzero Q (f P) (f R) v hv hvR hv0)
      simpa only [he] using hR
  · intro h v hv
    exact Or.inr ⟨P, h, hv⟩

def imageSubspace (W : Subspaces Q) : Subspaces Q :=
  ⟨imageSubmodule Q f l hinc W, by
    intro x hx
    rcases hx with rfl | ⟨P, _, hx⟩
    · exact Q.map_zero
    · exact (f P).property.2 x hx⟩

theorem imageSubspace_mono {W Z : Subspaces Q} (h : W.val ≤ Z.val) :
    (imageSubspace Q f l hinc W).val ≤ (imageSubspace Q f l hinc Z).val := by
  intro v hv
  rcases hv with hz | ⟨P, hP, hv⟩
  · exact Or.inl hz
  · exact Or.inr ⟨P, hP.trans h, hv⟩

theorem imageSubspace_reflects_le {W Z : Subspaces Q}
    (h : (imageSubspace Q f l hinc W).val ≤ (imageSubspace Q f l hinc Z).val) :
    W.val ≤ Z.val := by
  intro v hv
  by_cases hz : v = 0
  · exact hz ▸ Z.val.zero_mem
  let P := ray Q v hz (W.property v hv)
  have hp : P.val ≤ W.val := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
  have him := ((point_le_image_iff Q f l hinc W P).mpr hp).trans h
  exact ((point_le_image_iff Q f l hinc Z P).mp him) (Submodule.subset_span (by simp))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
