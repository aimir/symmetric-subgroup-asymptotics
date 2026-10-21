import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Data

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23
open BinaryRegularEightNaturalRegistry

theorem pair_bound (S L : Subrepresentation rho)
    (hproduct : binaryCoordinateProductSpan (charts 23).2.space S.toSubmodule ≤ L.toSubmodule) :
    Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 23).2.space S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation)) ≤ 6 := by
  obtain ⟨i, rfl⟩ := complete S
  obtain ⟨j, rfl⟩ := complete L
  have hc : compatible i j := by
    intro a b
    have hleft : (charts 23).2.inclusion (Pi.single a 1) ∈ (charts 23).2.space :=
      ⟨Pi.single a 1, rfl⟩
    have hright : (charts i).2.inclusion (Pi.single b 1) ∈ (states i).toSubmodule := by
      rw [states_space]
      exact ⟨Pi.single b 1, rfl⟩
    exact hproduct (binaryCoordinateProductSpan.product_mem _ _ _ hleft _ hright)
  obtain ⟨c, p, hi, hj⟩ := covered i j hc
  subst i
  subst j
  exact finite_pair_bound c p hproduct


/-- Width six forces these same original layer states. -/
theorem six_le_pair_head_forces_layers (S L : Subrepresentation rho)
    (hproduct : binaryCoordinateProductSpan (charts 23).2.space S.toSubmodule ≤ L.toSubmodule)
    (hwide : 6 ≤ Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 23).2.space S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation))) :
    S = states 46 ∧ L = states 45 := by
  obtain ⟨i, rfl⟩ := complete S
  obtain ⟨j, rfl⟩ := complete L
  have hc : compatible i j := by
    intro a b
    have hleft : (charts 23).2.inclusion (Pi.single a 1) ∈ (charts 23).2.space :=
      ⟨Pi.single a 1, rfl⟩
    have hright : (charts i).2.inclusion (Pi.single b 1) ∈ (states i).toSubmodule := by
      rw [states_space]
      exact ⟨Pi.single b 1, rfl⟩
    exact hproduct (binaryCoordinateProductSpan.product_mem _ _ _ hleft _ hright)
  obtain ⟨c, p, hi, hj⟩ := covered i j hc
  subst i
  subst j
  have hdim := denominator_dimension_le c p hproduct
  have hhead := coinvariants_finrank_le (sourceIndex c p)
  have hnum : (charts (denominatorIndex c p)).1 + 6 ≤
      headCeiling (sourceIndex c p) + (charts (targetIndex c p)).1 := by omega
  exact ⟨congrArg states (wide_indices c p hnum).1,
    congrArg states (wide_indices c p hnum).2⟩

end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23
