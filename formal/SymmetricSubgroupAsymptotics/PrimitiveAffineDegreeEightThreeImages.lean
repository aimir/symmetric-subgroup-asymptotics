import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupFixedFlags
import SymmetricSubgroupAsymptotics.BinaryThreeFixedFlagsConjugacy
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightNoFixedFlags

/-! Exact three-row recognition of the actual primitive affine degree-eight
complement image. Coverage comes from checked local adjunctions; each of the
other twelve rows is rejected by a checked invariant vector or dual vector. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise Matrix

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightThreeImages

abbrev Ambient := GeneralThreeTwoMatrixEncoding.Ambient

/-- Ordered as the fixed small-affine complement catalogue:7,21,168. -/
def models : Fin 3 → Subgroup Ambient :=
  ![GeneralThreeTwoActualSubgroupCoverage.rows 4,
    GeneralThreeTwoActualSubgroupCoverage.rows 14,
    GeneralThreeTwoActualSubgroupCoverage.rows 7]

variable {L Ω : Type} [Group L] [MulAction L Ω]
  [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω]
  (P : PrimitiveAffineProfile L Ω)

theorem coordinate_range_conjugate
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 3 → ZMod 2)) :
    ∃ i : Fin 3, ∃ c : Ambient,
      MulAut.conj c • (P.complementCoordinateMap x a).range = models i := by
  let phi := P.complementCoordinateMap x a
  obtain ⟨i, c, hc⟩ := GeneralThreeTwoActualSubgroupCoverage.complete phi.range
  have hi : i = 4 ∨ i = 7 ∨ i = 14 := by
    by_cases h4 : i = 4
    · exact Or.inl h4
    by_cases h7 : i = 7
    · exact Or.inr (Or.inl h7)
    by_cases h14 : i = 14
    · exact Or.inr (Or.inr h14)
    exfalso
    rcases GeneralThreeTwoSubgroupFixedFlags.row_flag i h4 h7 h14 with h | h
    · obtain ⟨v, hv, hfix⟩ := h
      obtain ⟨w, hw, hwhole⟩ := BinaryThreeInvariantSubspaces.fixed_vector_of_conjugate
        phi.range c v hv (fun g hg => hfix g (hc ▸ hg))
      exact P.coordinate_no_fixed_vector hprimitive x a w hw
        (fun k => hwhole (phi k) ⟨k, rfl⟩)
    · obtain ⟨v, hv, hfix⟩ := h
      obtain ⟨w, hw, hwhole⟩ := BinaryThreeInvariantSubspaces.fixed_covector_of_conjugate
        phi.range c v hv (fun g hg => hfix g (hc ▸ hg))
      exact P.coordinate_no_fixed_covector hprimitive x a w hw
        (fun k => hwhole (phi k) ⟨k, rfl⟩)
  rcases hi with rfl | rfl | rfl
  · exact ⟨0, c, hc⟩
  · exact ⟨2, c, hc⟩
  · exact ⟨1, c, hc⟩

theorem complement_model_of_coordinates
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 3 → ZMod 2)) :
    ∃ i : Fin 3, Nonempty (P.complement x ≃* models i) := by
  obtain ⟨i, c, hc⟩ := coordinate_range_conjugate P hprimitive x a
  change (P.complementCoordinateMap x a).range.map (MulAut.conj c).toMonoidHom =
    models i at hc
  exact ⟨i, ⟨(MonoidHom.ofInjective (P.complementCoordinateMap_injective x a)).trans
    (((MulAut.conj c).subgroupMap _).trans (MulEquiv.subgroupCongr hc))⟩⟩

theorem complement_model
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω) (hdegree : Nat.card Ω = 8) :
    ∃ i : Fin 3, Nonempty (P.complement x ≃* models i) := by
  obtain ⟨a⟩ := P.translationCoordinates_degreeEight_nonempty hprimitive x hdegree
  exact complement_model_of_coordinates P hprimitive x a

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightThreeImages

end
