import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceEquivalence

/-! Opposition of actual singular subspaces is recovered from point
incidence. A maximal-dimensional singular space has no nonzero singular
orthogonal vector outside it; consequently two disjoint such spaces pair
nondegenerately. No building or polar-space recognition is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (B : LinearMap.BilinForm K V)

theorem inf_eq_bot_iff_no_common_point (W Z : Subspaces B) :
    (W.val ⊓ Z.val : Submodule K V)=⊥ ↔
      ¬∃P : Points B,P.val ≤ W.val ∧ P.val ≤ Z.val := by
  constructor
  · rintro h ⟨P,hP,hQ⟩
    obtain ⟨v,hv,hv0⟩ := point_nonzero B P
    have hm : v∈(⊥ : Submodule K V) := h ▸ (show v∈W.val⊓Z.val from ⟨hP hv,hQ hv⟩)
    exact hv0 hm
  · intro h
    apply le_antisymm _ bot_le
    intro v hv
    change v=0
    by_contra hn
    let P := ray B v hn (W.property v hv.1 v hv.1)
    exact h ⟨P,(Submodule.span_singleton_le_iff_mem _ _).mpr hv.1,
      (Submodule.span_singleton_le_iff_mem _ _).mpr hv.2⟩

theorem imageSubspace_inf_eq_bot_iff (f : Points B≃Points B) (l : Planes B≃Planes B)
    (hinc : ∀P L,(f P).val ≤ (l L).val ↔ P.val ≤ L.val)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)
    (W Z : Subspaces B) :
    ((imageSubspace B f l hinc horth W).val ⊓
      (imageSubspace B f l hinc horth Z).val : Submodule K V)=⊥ ↔
      (W.val ⊓ Z.val : Submodule K V)=⊥ := by
  rw [inf_eq_bot_iff_no_common_point,inf_eq_bot_iff_no_common_point]
  constructor
  · intro h ⟨P,hP,hQ⟩
    exact h ⟨f P,(point_le_image_iff B f l hinc W P).mpr hP,
      (point_le_image_iff B f l hinc Z P).mpr hQ⟩
  · intro h ⟨P,hP,hQ⟩
    have hw := point_le_image_iff B f l hinc W (f.symm P)
    have hz := point_le_image_iff B f l hinc Z (f.symm P)
    simp only [f.apply_symm_apply] at hw hz
    exact h ⟨f.symm P,hw.mp hP,hz.mp hQ⟩

theorem orthogonal_singular_vector_mem (hs : ∀x y,B x y=B y x) (d : ℕ)
    (hbound : ∀T : Subspaces B,Module.finrank K T.val ≤ d)
    (Z : Subspaces B) (hZ : Module.finrank K Z.val=d)
    (v : V) (hv : B v v=0) (hz : ∀z∈Z.val,B v z=0) : v∈Z.val := by
  let L : Submodule K V := Submodule.span K {v}
  have hL : ZeroOn B L L := by
    intro x hx y hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [map_smul,LinearMap.smul_apply,hv,smul_zero]
  have hcross : ZeroOn B L Z.val := by
    intro x hx z hz'
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [map_smul,LinearMap.smul_apply,hz z hz',smul_zero]
  let T : Subspaces B := ⟨L⊔Z.val,CFSGSingularPairSpan.zeroOn_sup B hs L Z.val hL Z.property hcross⟩
  have he : Z.val=T.val := Submodule.eq_of_le_of_finrank_le le_sup_right
    (by rw [hZ];exact hbound T)
  rw [he]
  exact (show L≤T.val from le_sup_left) (Submodule.mem_span_singleton_self v)

theorem opposed_pair_left_nondegenerate (hs : ∀x y,B x y=B y x) (d : ℕ)
    (hbound : ∀T : Subspaces B,Module.finrank K T.val ≤ d)
    (W Z : Subspaces B) (hZ : Module.finrank K Z.val=d)
    (hdisjoint : (W.val⊓Z.val : Submodule K V)=⊥)
    (v : V) (hv : v∈W.val) (hz : ∀z∈Z.val,B v z=0) : v=0 := by
  have hmem := orthogonal_singular_vector_mem B hs d hbound Z hZ v (W.property v hv v hv) hz
  exact (show v∈(⊥ : Submodule K V) from hdisjoint ▸ ⟨hv,hmem⟩)

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
