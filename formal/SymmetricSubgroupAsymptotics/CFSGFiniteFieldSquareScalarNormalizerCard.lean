import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareScalarNormalizer
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizerCard

/-! The same actual finite-field automorphism factor bounds square-scalar
normalizers, including odd characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
variable (K : Type*) [Field K] [Finite K]

theorem card_squareScalarNormalizer_le :
    Nat.card (Subgroup.normalizer (squareScalarSubgroup K : Set (AddAut K)))≤
      Nat.card Kˣ*Nat.card (K ≃+* K) := by
  let j := Subgroup.inclusion (square_scalar_normalizer_le_scalar_normalizer (K:=K))
  exact (Nat.card_le_card_of_injective j (Subgroup.inclusion_injective _)).trans
    (card_scalarNormalizer_le K)

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
