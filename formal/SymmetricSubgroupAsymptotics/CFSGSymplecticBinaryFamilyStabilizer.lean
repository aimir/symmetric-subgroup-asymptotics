import SymmetricSubgroupAsymptotics.CFSGRootFamilyStabilizer
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRootFamilyImages
import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGSymplecticPointRootLabels

/-! The subgroup of actual projective symplectic automorphisms preserving
the natural point-root family has index at most three in characteristic
two. Stability is proved for the SAME original projective root labels. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices CFSGNormalizerCenterAtoms
variable {K : Type} [Field K]

theorem projectiveNaturalRootLine_conjugation (r : ℕ) (hr : 0 < r)
    (g : elementaryRootGroup K (r + 1)) (v : Index (r + 1) → K) :
    let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
    (projectiveNaturalRootLine r hr v).map (MulAut.conj (q g)).toMonoidHom =
      projectiveNaturalRootLine r hr ((g.val : Mat K (r + 1)) *ᵥ v) := by
  dsimp only
  ext y
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    exact (projectiveNaturalRootElement_conjugation r hr g v a.toAdd).symm
  · rintro ⟨a, rfl⟩
    refine ⟨projectiveNaturalRootHom r hr v a, ⟨a, rfl⟩, ?_⟩
    exact projectiveNaturalRootElement_conjugation r hr g v a.toAdd

theorem innerFamily_first_projectiveNaturalRootLine (r : ℕ) (hr : 0 < r) :
    innerFamily (projectiveNaturalRootLine (K := K) r hr
      (Pi.single (Sum.inl (0 : Fin (r + 1))) 1)) =
      Set.range (fun v : {v : Index (r + 1) → K // v ≠ 0} =>
        projectiveNaturalRootLine r hr v.val) := by
  let v₀ : Index (r + 1) → K := Pi.single (Sum.inl (0 : Fin (r + 1))) 1
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have he := congrFun h (Sum.inl 0)
    have hzero : (1 : K) = 0 := by
      simpa only [v₀, Pi.single_eq_same, Pi.zero_apply] using he
    exact one_ne_zero hzero
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  ext H
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (elementaryRootGroup K (r + 1))) g
    refine ⟨⟨(g.val : Mat K (r + 1)) *ᵥ v₀,
      elementary_mulVec_ne_zero _ g v₀ hv₀⟩, ?_⟩
    exact (projectiveNaturalRootLine_conjugation r hr g v₀).symm
  · rintro ⟨v, rfl⟩
    obtain ⟨g, hg⟩ := exists_elementary_mulVec_first_basis K r hr v.val v.property
    refine ⟨q g, ?_⟩
    have he := projectiveNaturalRootLine_conjugation r hr g v₀
    change (projectiveNaturalRootLine r hr v₀).map (MulAut.conj (q g)).toMonoidHom =
      projectiveNaturalRootLine r hr ((g.val : Mat K (r + 1)) *ᵥ v₀) at he
    rw [hg] at he
    exact he.symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry CFSGNormalizerCenterAtoms
variable {K : Type} [Field K]

def naturalRootFamilyStabilizer (r : ℕ) (hr : 0 < r) :
    Subgroup (MulAut (elementaryProjective K (r + 1))) :=
  familyStabilizer (projectiveNaturalRootLine r hr
    (Pi.single (Sum.inl (0 : Fin (r + 1))) 1))

theorem naturalRootFamilyStabilizer_stable (r : ℕ) (hr : 0 < r)
    (f : naturalRootFamilyStabilizer (K := K) r hr)
    (v : Index (r + 1) → K) (hv : v ≠ 0) :
    ∃ w : Index (r + 1) → K, w ≠ 0 ∧
      projectiveNaturalRootLine r hr w =
        (projectiveNaturalRootLine r hr v).map f.val.toMonoidHom := by
  have hm : projectiveNaturalRootLine r hr v ∈
      innerFamily (projectiveNaturalRootLine r hr
        (Pi.single (Sum.inl (0 : Fin (r + 1))) 1)) := by
    rw [innerFamily_first_projectiveNaturalRootLine]
    exact ⟨⟨v, hv⟩, rfl⟩
  have hi := map_mem_innerFamily_of_stabilizer _ _ f hm
  rw [innerFamily_first_projectiveNaturalRootLine] at hi
  obtain ⟨w, hw⟩ := hi
  exact ⟨w.val, w.property, hw⟩

theorem naturalRootFamilyStabilizer_point_stable (r : ℕ) (hr : 0 < r)
    (f : naturalRootFamilyStabilizer (K := K) r hr)
    (x : CFSGSymplecticPointRootLabels.Points (K := K) r) :
    ∃ y, CFSGSymplecticPointRootLabels.label r hr y =
      (CFSGSymplecticPointRootLabels.label r hr x).map f.val.toMonoidHom := by
  obtain ⟨w, hw, he⟩ := naturalRootFamilyStabilizer_stable r hr f x.rep x.rep_nonzero
  exact ⟨Projectivization.mk K w hw,
    (CFSGSymplecticPointRootLabels.label_mk r hr w hw).trans he⟩

theorem binaryChar_naturalRootFamilyStabilizer_index_le_three
    [Finite K] [CharP K 2] (r : ℕ) (hr : 0 < r) :
    (naturalRootFamilyStabilizer (K := K) r hr).index ≤ 3 := by
  rw [naturalRootFamilyStabilizer, familyStabilizer_index]
  exact binaryChar_naturalRoot_family_image_card_le_three r hr

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
