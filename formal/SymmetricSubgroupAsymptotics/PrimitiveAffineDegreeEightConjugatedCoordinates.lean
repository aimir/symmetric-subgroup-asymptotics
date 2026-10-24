import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightThreeImages

/-! Absorb the proved actual matrix conjugator into the original
translation chart. The resulting complement range is literally one of
the three checked models, with the original conjugation action retained. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {G X : Type} [Group G] [MulAction G X]
    (P : PrimitiveAffineProfile G X)

theorem complementCoordinateMap_change_chart (x : X)
    (a : P.V ≃* Multiplicative (Fin 3 → ZMod 2))
    (c : GeneralThreeTwoMatrixEncoding.Ambient) :
    P.complementCoordinateMap x
      (a.trans ((ElementaryZModAutomorphismCoordinates.matrixEquiv 2 3).symm c)) =
      (MulAut.conj c).toMonoidHom.comp (P.complementCoordinateMap x a) := by
  let M := ElementaryZModAutomorphismCoordinates.matrixEquiv 2 3
  let u := M.symm c
  apply MonoidHom.ext
  intro h
  have hu : (MulAut.congr (a.trans u)) (P.complementAction x h) =
      u * (MulAut.congr a) (P.complementAction x h) * u⁻¹ := by
    apply MulEquiv.ext
    intro v
    rfl
  change M ((MulAut.congr (a.trans u)) (P.complementAction x h)) =
    c * M ((MulAut.congr a) (P.complementAction x h)) * c⁻¹
  rw [hu,map_mul,map_mul,map_inv]
  have hc : M u = c := M.apply_symm_apply c
  rw [hc]

theorem exists_coordinates_range_model
    [Finite G] [Finite X] [Nontrivial X] [FaithfulSMul G X]
    (hprimitive : MulAction.IsPreprimitive G X) (x : X) (hdegree : Nat.card X = 8) :
    ∃ i : Fin 3, ∃ a : P.V ≃* Multiplicative (Fin 3 → ZMod 2),
      (P.complementCoordinateMap x a).range =
        PrimitiveAffineDegreeEightThreeImages.models i := by
  obtain ⟨a⟩ := P.translationCoordinates_degreeEight_nonempty hprimitive x hdegree
  obtain ⟨i,c,hc⟩ :=
    PrimitiveAffineDegreeEightThreeImages.coordinate_range_conjugate P hprimitive x a
  refine ⟨i,a.trans ((ElementaryZModAutomorphismCoordinates.matrixEquiv 2 3).symm c),?_⟩
  rw [P.complementCoordinateMap_change_chart,MonoidHom.range_comp]
  exact hc

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
