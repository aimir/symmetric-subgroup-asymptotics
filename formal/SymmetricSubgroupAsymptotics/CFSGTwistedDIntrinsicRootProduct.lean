import SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneFamilyAction

/-! Intrinsic root elements and the commuting/root-product test in
the actual relative central quotient. All abstract automorphisms
preserve this test. Its identification with quadratic Grassmann
adjacency is a separate concrete geometric theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDIntrinsicRootProduct
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDPlaneRootLine
open CFSGTwistedDRootPlaneImage CFSGTwistedDProjectivePlaneLabel
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDProjectiveRootFamily
open CFSGTwistedDPlaneFamilyAction CFSGTwistedA2FixedField

def IsRootElement (s : ℕ) (q : CFSG.PrimePower) (x : relativeRootGroup (s + 2) q) : Prop :=
  ∃ g : relativeRootGroup (s + 2) q, ∃ a : fixedField q, x = g * highestRoot s q a * g⁻¹

def IsProjectiveRootElement (s : ℕ) (q : CFSG.PrimePower) (x : Projective s q) : Prop :=
  ∃ y : relativeRootGroup (s + 2) q, IsRootElement s q y ∧ projection s q y = x

theorem isProjectiveRootElement_iff_mem_rootLine (s : ℕ) (q : CFSG.PrimePower)
    (x : Projective s q) :
    IsProjectiveRootElement s q x ↔ ∃ g : Projective s q, x ∈ projectiveConjugateRootLine s q g := by
  constructor
  · rintro ⟨y, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨projection s q g, ?_⟩
    rw [← map_conjugateRootLine]
    exact ⟨g * highestRoot s q a * g⁻¹,
      (mem_conjugateRootLine_iff s q g _).mpr ⟨a, rfl⟩, rfl⟩
  · rintro ⟨g, hx⟩
    obtain ⟨u, rfl⟩ := (QuotientGroup.mk'_surjective
      (Subgroup.center (relativeRootGroup (s + 2) q))) g
    change x ∈ projectiveConjugateRootLine s q (projection s q u) at hx
    rw [← map_conjugateRootLine] at hx
    obtain ⟨y, hy, he⟩ := hx
    obtain ⟨a, ha⟩ := (mem_conjugateRootLine_iff s q u y).mp hy
    exact ⟨y, ⟨u, a, ha⟩, he⟩

theorem automorphism_isProjectiveRootElement (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (x : Projective s q) (hx : IsProjectiveRootElement s q x) :
    IsProjectiveRootElement s q (f x) := by
  obtain ⟨g, hg⟩ := (isProjectiveRootElement_iff_mem_rootLine s q x).mp hx
  obtain ⟨h, hh⟩ := automorphism_maps_projectiveConjugateRootLine s q f g
  have hm : f x ∈ (projectiveConjugateRootLine s q g).map f.toMonoidHom := ⟨x, hg, rfl⟩
  rw [hh] at hm
  exact (isProjectiveRootElement_iff_mem_rootLine s q (f x)).mpr ⟨h, hm⟩

theorem automorphism_isProjectiveRootElement_iff (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (x : Projective s q) :
    IsProjectiveRootElement s q (f x) ↔ IsProjectiveRootElement s q x := by
  constructor
  · intro hx
    have h := automorphism_isProjectiveRootElement s q f.symm (f x) hx
    simpa only [MulEquiv.symm_apply_apply] using h
  · exact automorphism_isProjectiveRootElement s q f x

def RootProductRelation (s : ℕ) (q : CFSG.PrimePower) (L M : Subgroup (Projective s q)) : Prop :=
  ∃ x ∈ L, x ≠ 1 ∧ ∃ y ∈ M, y ≠ 1 ∧ Commute x y ∧ IsProjectiveRootElement s q (x * y)

theorem automorphism_maps_RootProductRelation (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (L M : Subgroup (Projective s q))
    (h : RootProductRelation s q L M) :
    RootProductRelation s q (L.map f.toMonoidHom) (M.map f.toMonoidHom) := by
  obtain ⟨x, hx, hxn, y, hy, hyn, hc, hp⟩ := h
  refine ⟨f x, ⟨x, hx, rfl⟩, ?_, f y, ⟨y, hy, rfl⟩, ?_, ?_, ?_⟩
  · intro he
    exact hxn (f.injective (he.trans f.map_one.symm))
  · intro he
    exact hyn (f.injective (he.trans f.map_one.symm))
  · change f x * f y = f y * f x
    simpa only [map_mul] using congrArg f hc.eq
  · simpa only [map_mul] using automorphism_isProjectiveRootElement s q f (x * y) hp

private theorem map_symm_map (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (L : Subgroup (Projective s q)) :
    (L.map f.toMonoidHom).map f.symm.toMonoidHom = L := by
  have he : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact f.symm_apply_apply x
  rw [Subgroup.map_map, he, Subgroup.map_id]

theorem automorphism_RootProductRelation_iff (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (L M : Subgroup (Projective s q)) :
    RootProductRelation s q (L.map f.toMonoidHom) (M.map f.toMonoidHom) ↔
      RootProductRelation s q L M := by
  constructor
  · intro h
    have hh := automorphism_maps_RootProductRelation s q f.symm _ _ h
    rw [map_symm_map, map_symm_map] at hh
    exact hh
  · exact automorphism_maps_RootProductRelation s q f L M

theorem singularAction_RootProductRelation_iff (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (P Q : SingularPlanes s q) :
    RootProductRelation s q (singularLabel s q (singularActionHom s q f P))
      (singularLabel s q (singularActionHom s q f Q)) ↔
      RootProductRelation s q (singularLabel s q P) (singularLabel s q Q) := by
  rw [singularLabel_action, singularLabel_action]
  exact automorphism_RootProductRelation_iff s q f _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedDIntrinsicRootProduct
