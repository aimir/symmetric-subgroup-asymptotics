import SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints

/-! A literal point/plane incidence equivalence transports every singular
subspace. Closure under addition is proved from the actual plane map;
the image is not assumed to be a linear subspace. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (B : LinearMap.BilinForm K V) (f : Points B≃Points B) (l : Planes B≃Planes B)
    (hinc : ∀P L,(f P).val ≤ (l L).val ↔ P.val ≤ L.val)

def imageSubmodule (W : Subspaces B) : Submodule K V where
  carrier := {v | v=0 ∨ ∃P : Points B,P.val ≤ W.val ∧ v∈(f P).val}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (rfl|⟨P,hP,hx⟩) (rfl|⟨Q,hQ,hy⟩)
    · exact Or.inl (zero_add 0)
    · exact Or.inr ⟨Q,hQ,by simpa only [zero_add] using hy⟩
    · exact Or.inr ⟨P,hP,by simpa only [add_zero] using hx⟩
    by_cases hz : x+y=0
    · exact Or.inl hz
    by_cases he : P=Q
    · subst Q
      exact Or.inr ⟨P,hP,(f P).val.add_mem hx hy⟩
    let L := joinPlane B W P Q hP hQ he
    have hpL : P.val ≤ L.val := le_sup_left
    have hqL : Q.val ≤ L.val := le_sup_right
    have hxy : x+y∈(l L).val := (l L).val.add_mem ((hinc P L).mpr hpL hx)
      ((hinc Q L).mpr hqL hy)
    let R := ray B (x+y) hz ((l L).property.2 (x+y) hxy (x+y) hxy)
    have hr : R.val ≤ (l L).val := (Submodule.span_singleton_le_iff_mem _ _).mpr hxy
    have hi : (f.symm R).val ≤ L.val := (hinc (f.symm R) L).mp (by
      simpa only [f.apply_symm_apply] using hr)
    refine Or.inr ⟨f.symm R,hi.trans (sup_le hP hQ),?_⟩
    rw [f.apply_symm_apply]
    exact Submodule.subset_span (by simp)
  smul_mem' := by
    intro a v hv
    rcases hv with rfl|⟨P,hP,hv⟩
    · exact Or.inl (smul_zero a)
    · exact Or.inr ⟨P,hP,(f P).val.smul_mem a hv⟩

theorem point_le_image_iff (W : Subspaces B) (P : Points B) :
    (f P).val ≤ imageSubmodule B f l hinc W ↔ P.val ≤ W.val := by
  constructor
  · intro h
    obtain ⟨v,hv,hv0⟩ := point_nonzero B (f P)
    rcases h hv with hz|⟨Q,hQ,hvQ⟩
    · exact False.elim (hv0 hz)
    · have he := f.injective (point_eq_of_common_nonzero B (f P) (f Q) v hv hvQ hv0)
      simpa only [he] using hQ
  · intro h v hv
    exact Or.inr ⟨P,h,hv⟩

variable (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)

def imageSubspace (W : Subspaces B) : Subspaces B :=
  ⟨imageSubmodule B f l hinc W,by
    intro x hx y hy
    rcases hx with rfl|⟨P,hP,hx⟩
    · simp
    rcases hy with rfl|⟨Q,hQ,hy⟩
    · simp
    exact ((horth P Q).mpr (fun a ha b hb=>W.property a (hP ha) b (hQ hb))) x hx y hy⟩

theorem imageSubspace_mono {W Z : Subspaces B} (h : W.val ≤ Z.val) :
    (imageSubspace B f l hinc horth W).val ≤ (imageSubspace B f l hinc horth Z).val := by
  intro v hv
  rcases hv with hz|⟨P,hP,hv⟩
  · exact Or.inl hz
  · exact Or.inr ⟨P,hP.trans h,hv⟩

theorem imageSubspace_reflects_le {W Z : Subspaces B}
    (h : (imageSubspace B f l hinc horth W).val ≤ (imageSubspace B f l hinc horth Z).val) :
    W.val ≤ Z.val := by
  intro v hv
  by_cases hz : v=0
  · exact hz ▸ Z.val.zero_mem
  let P := ray B v hz (W.property v hv v hv)
  have hp : P.val ≤ W.val := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
  have him := ((point_le_image_iff B f l hinc W P).mpr hp).trans h
  exact ((point_le_image_iff B f l hinc Z P).mp him) (Submodule.subset_span (by simp))

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
