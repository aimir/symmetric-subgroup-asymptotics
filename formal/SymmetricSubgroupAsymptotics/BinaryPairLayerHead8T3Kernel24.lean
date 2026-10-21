import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel24Data

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel24
open BinaryRegularEightNaturalRegistry

theorem pair_bound (S L : Subrepresentation rho)
    (hproduct : binaryCoordinateProductSpan (charts 24).2.space S.toSubmodule ≤ L.toSubmodule) :
    Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 24).2.space S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation)) ≤ 3 := by
  obtain ⟨i, rfl⟩ := complete S
  obtain ⟨j, rfl⟩ := complete L
  have hc : compatible i j := by
    intro a b
    have hleft : (charts 24).2.inclusion (Pi.single a 1) ∈ (charts 24).2.space :=
      ⟨Pi.single a 1, rfl⟩
    have hright : (charts i).2.inclusion (Pi.single b 1) ∈ (states i).toSubmodule := by
      rw [states_space]
      exact ⟨Pi.single b 1, rfl⟩
    exact hproduct (binaryCoordinateProductSpan.product_mem _ _ _ hleft _ hright)
  obtain ⟨p, hi, hj⟩ := covered i j hc
  subst i
  subst j
  exact finite_pair_bound p hproduct

end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel24
