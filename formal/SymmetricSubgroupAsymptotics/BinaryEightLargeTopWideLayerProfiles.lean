import SymmetricSubgroupAsymptotics.BinaryPairHighLayerDistinctness
import SymmetricSubgroupAsymptotics.BinaryEightTop29HighHeadKernel
import SymmetricSubgroupAsymptotics.BinaryEightTop31HighHeadKernel

/-! Exact actual layer profiles above the literal29 and31 eight-point
actions. The unique high-head space excludes29; the two different31
spaces give total dimension ten. No sixteen-point group census is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics

namespace BinaryEightTop29HighHeadKernel

theorem pair_layer_bound_three
    (K : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (hconstant : (1 : Fin 8 → ZMod 2) ∈ K)
    (hcap : ∀ A : Subrepresentation BinaryEightTop29CoordinateAction.rho,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 2)
    (S L : Subrepresentation BinaryEightTop29CoordinateAction.rho)
    (_hproduct : binaryCoordinateProductSpan K S.toSubmodule ≤ L.toSubmodule) :
    Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation)) ≤ 3 := by
  by_contra hbad
  obtain ⟨hs, hl, hne⟩ := binary_head_four_pair_layer_profile
    BinaryEightTop29CoordinateAction.rho K hconstant S L (hcap S) (hcap L) (Nat.succ_le_of_lt (Nat.lt_of_not_ge hbad))
  exact hne ((high_head_space S (by omega)).trans (high_head_space L (by omega)).symm)

end BinaryEightTop29HighHeadKernel
namespace BinaryEightTop31HighHeadKernel

theorem pair_layer_head_four_dimension_ten
    (K : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (hconstant : (1 : Fin 8 → ZMod 2) ∈ K)
    (hcap : ∀ A : Subrepresentation BinaryEightTop31CoordinateAction.rho,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 2)
    (S L : Subrepresentation BinaryEightTop31CoordinateAction.rho)
    (_hproduct : binaryCoordinateProductSpan K S.toSubmodule ≤ L.toSubmodule)
    (hhead : 4 ≤ Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation))) :
    Module.finrank (ZMod 2) S.toSubmodule + Module.finrank (ZMod 2) L.toSubmodule = 10 := by
  obtain ⟨hs, hl, hne⟩ := binary_head_four_pair_layer_profile
    BinaryEightTop31CoordinateAction.rho K hconstant S L (hcap S) (hcap L) hhead
  rcases high_head_space S (by omega) with hs | hs <;>
    rcases high_head_space L (by omega) with hl | hl
  · exact (hne (hs.trans hl.symm)).elim
  · rw [hs, hl, BinaryRegularEightNaturalRegistry.chart44.finrank,
      BinaryRegularEightNaturalRegistry.chart45.finrank]
  · rw [hs, hl, BinaryRegularEightNaturalRegistry.chart45.finrank,
      BinaryRegularEightNaturalRegistry.chart44.finrank]
  · exact (hne (hs.trans hl.symm)).elim

end BinaryEightTop31HighHeadKernel
end SymmetricSubgroupAsymptotics
