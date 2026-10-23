import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalSingularGallery
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarSemilinearPiece

/-! Ranges of genuine local linear representatives are actual singular
spaces of the same dimension. A maximal domain has maximal range;
disjoint domains have disjoint ranges because their rays are carried by
the SAME injective point permutation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticPieceRanges
open CFSGQuadraticMaximalSingularGallery CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local instance : RingHomSurjective (RingEquiv.refl K).toRingHom :=
  ⟨fun x => ⟨x, rfl⟩⟩

theorem range_singular (Q : QuadraticForm K V) (f : Points Q ≃ Points Q)
    (W : Subspaces Q) (F : SemilinearPiece Q f W (RingEquiv.refl K)) :
    ∀ z ∈ F.map.range, Q z = 0 := by
  rintro z ⟨x, rfl⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, QuadraticMap.map_zero]
  · have he := F.point x hx
    have hm : F.map x ∈
        (f (ray Q x.val (fun h => hx (Subtype.ext h)) (W.property x.val x.property))).val := by
      rw [← he]
      exact Submodule.mem_span_singleton_self _
    exact (f _).property.2 _ hm

theorem range_finrank (Q : QuadraticForm K V) (f : Points Q ≃ Points Q)
    (W : Subspaces Q) (F : SemilinearPiece Q f W (RingEquiv.refl K)) :
    Module.finrank K F.map.range = Module.finrank K W.val :=
  LinearMap.finrank_range_of_inj F.injective

theorem range_maximal (Q : QuadraticForm K V) (f : Points Q ≃ Points Q)
    (W : Subspaces Q) (hW : MaximalSingular Q W.val)
    (F : SemilinearPiece Q f W (RingEquiv.refl K)) : MaximalSingular Q F.map.range := by
  have hs := range_singular Q f W F
  obtain ⟨M, hRM, hM⟩ := exists_maximal_ge Q F.map.range hs
  have hd : Module.finrank K M = Module.finrank K F.map.range :=
    (maximal_finrank_eq Q ⟨M, hM⟩ ⟨W.val, hW⟩).trans (range_finrank Q f W F).symm
  have he : F.map.range = M := Submodule.eq_of_le_of_finrank_le hRM hd.le
  exact he.symm ▸ hM

theorem ranges_disjoint (Q : QuadraticForm K V) (f : Points Q ≃ Points Q)
    (W Z : Subspaces Q) (hWZ : Disjoint W.val Z.val)
    (F : SemilinearPiece Q f W (RingEquiv.refl K))
    (G : SemilinearPiece Q f Z (RingEquiv.refl K)) : Disjoint F.map.range G.map.range := by
  classical
  apply Submodule.disjoint_def.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  by_contra hz
  have hx0 : x ≠ 0 := by
    intro he
    have hm : F.map x = 0 := by rw [he, map_zero]
    exact hz (hx.symm.trans hm)
  have hy0 : y ≠ 0 := by
    intro he
    have hm : G.map y = 0 := by rw [he, map_zero]
    exact hz (hy.symm.trans hm)
  let P := ray Q x.val (fun h => hx0 (Subtype.ext h)) (W.property x.val x.property)
  let R := ray Q y.val (fun h => hy0 (Subtype.ext h)) (Z.property y.val y.property)
  have hzP : z ∈ (f P).val := by
    rw [← F.point x hx0, ← hx]
    exact Submodule.mem_span_singleton_self _
  have hzR : z ∈ (f R).val := by
    rw [← G.point y hy0, ← hy]
    exact Submodule.mem_span_singleton_self _
  have hPR : P = R := f.injective (point_eq_of_common_nonzero Q (f P) (f R) z hzP hzR hz)
  have hm : x.val ∈ Submodule.span K {y.val} := by
    have he := congrArg Subtype.val hPR
    change Submodule.span K {x.val} = Submodule.span K {y.val} at he
    rw [← he]
    exact Submodule.mem_span_singleton_self _
  have hxZ : x.val ∈ Z.val := ((Submodule.span_singleton_le_iff_mem _ _).mpr y.property) hm
  have he : x.val = 0 := (Submodule.disjoint_def.mp hWZ) x.val x.property hxZ
  exact hx0 (Subtype.ext he)

end SymmetricSubgroupAsymptotics.CFSGQuadraticPieceRanges
