import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel14Data

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel14
open BinaryHeisenbergEightNaturalHeads

theorem pair_bound (S L : Subrepresentation rho)
    (hproduct : binaryCoordinateProductSpan (charts 14).2.space S.toSubmodule ≤ L.toSubmodule) :
    Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 14).2.space S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation)) ≤ 4 := by
  obtain ⟨i, rfl⟩ := complete S
  obtain ⟨j, rfl⟩ := complete L
  have hc : compatible i j := by
    intro a b
    have hleft : (charts 14).2.inclusion (Pi.single a 1) ∈ (charts 14).2.space :=
      ⟨Pi.single a 1, rfl⟩
    have hright : (charts i).2.inclusion (Pi.single b 1) ∈ (states i).toSubmodule := by
      rw [states_space]
      exact ⟨Pi.single b 1, rfl⟩
    exact hproduct (binaryCoordinateProductSpan.product_mem _ _ _ hleft _ hright)
  obtain ⟨p, hi, hj⟩ := covered i j hc
  subst i
  subst j
  exact finite_pair_bound p hproduct

/-- Width four forces these same original layer states. -/
theorem four_le_pair_head_forces_layers (S L : Subrepresentation rho)
    (hproduct : binaryCoordinateProductSpan (charts 14).2.space S.toSubmodule ≤ L.toSubmodule)
    (hwide : 4 ≤ Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 14).2.space S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation))) :
    (S = states 14 ∧ L = states 12) := by
  obtain ⟨i, rfl⟩ := complete S
  obtain ⟨j, rfl⟩ := complete L
  have hc : compatible i j := by
    intro a b
    have hleft : (charts 14).2.inclusion (Pi.single a 1) ∈ (charts 14).2.space :=
      ⟨Pi.single a 1, rfl⟩
    have hright : (charts i).2.inclusion (Pi.single b 1) ∈ (states i).toSubmodule := by
      rw [states_space]
      exact ⟨Pi.single b 1, rfl⟩
    exact hproduct (binaryCoordinateProductSpan.product_mem _ _ _ hleft _ hright)
  obtain ⟨p, hi, hj⟩ := covered i j hc
  subst i
  subst j
  have hdim := denominator_dimension_le p hproduct
  have hhead := coinvariants_finrank_le (sourceIndex p)
  have hnum : (charts (denominatorIndex p)).1 + 4 ≤
      headCeiling (sourceIndex p) + (charts (targetIndex p)).1 := by omega
  exact ⟨congrArg states (wide_indices p hnum).1,
    congrArg states (wide_indices p hnum).2⟩


end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel14
