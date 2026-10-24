import SymmetricSubgroupAsymptotics.CFSGSymplecticFixedFreeClassCodes
import SymmetricSubgroupAsymptotics.SymplecticSelfReciprocalCode
import SymmetricSubgroupAsymptotics.MatrixUnitCharacteristicPolynomial
import SymmetricSubgroupAsymptotics.BinaryFixedFreePrimaryDegree
import SymmetricSubgroupAsymptotics.LinearMapPrimaryWeightedCode

/-! Actual polynomial indices and primary-factor mass bounds for the
original elementary symplectic representation. The binary fixed-free
mass is at most r; the unrestricted mass is at most 2r. Both are read
from the SAME original operator and its actual primary chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix Classical

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPrimaryCodeData
open CFSGSymplecticSerreMatrices CFSGSymplecticPointAffineHom
open CFSGSymplecticStabilizerCoordinates CFSGSymplecticFixedFreeClassCodes
open Polynomial UniqueFactorizationMonoid
variable (K : Type) [Field K]

def linearUnit (r : ℕ) (g : elementaryRootGroup K r) :
    LinearMap.GeneralLinearGroup K (Index r → K) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (naturalLinearHom K r g)

theorem linearUnit_charpoly (r : ℕ) (g : elementaryRootGroup K r) :
    (linearUnit K r g : Module.End K (Index r → K)).charpoly =
      (g.val : Mat K r).charpoly :=
  MatrixUnitCharacteristicPolynomial.naturalLinearHom_charpoly K (Index r)
    (elementaryRootGroup K r) g

abbrev PolynomialIndex (r : ℕ) :=
  Set.range (fun g : Matrix.symplecticGroup (Fin r) K => (g : Mat K r).charpoly)

instance finitePolynomialIndex [Finite K] (r : ℕ) : Finite (PolynomialIndex K r) := by
  letI : Finite (Matrix.symplecticGroup (Fin r) K) :=
    Finite.of_injective (fun g : Matrix.symplecticGroup (Fin r) K => g.val)
      Subtype.val_injective
  exact Finite.of_surjective
    (Set.rangeFactorization (fun g : Matrix.symplecticGroup (Fin r) K =>
      (g : Mat K r).charpoly)) Set.rangeFactorization_surjective

def polynomialIndex (r : ℕ) (g : elementaryRootGroup K r) : PolynomialIndex K r :=
  ⟨(g.val : Mat K r).charpoly, elementaryToSymplectic K r g, rfl⟩

theorem linearUnit_charpoly_eq_index (r : ℕ) (g : elementaryRootGroup K r) :
    (linearUnit K r g : Module.End K (Index r → K)).charpoly =
      (polynomialIndex K r g).val := linearUnit_charpoly K r g

theorem normalizedFactor_mass_le (r : ℕ) (g : elementaryRootGroup K r) :
    (normalizedFactors (linearUnit K r g : Module.End K (Index r → K)).charpoly).card ≤
      2*r := by
  let A := (linearUnit K r g : Module.End K (Index r → K))
  let C := LinearMapPositivePrimaryDecomposition.chart A
  rw [LinearMapPrimaryWeightedCode.normalizedFactors_card C]
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_sum,Fintype.card_fin,two_mul]
    using C.exponent_sum_le_dimension

theorem polynomialIndex_card_le [Finite K] [CharP K 2] (r : ℕ) :
    Nat.card (PolynomialIndex K r) ≤ Nat.card K ^ r := by
  simpa only [Fintype.card_fin] using
    (SymplecticSelfReciprocalCode.card_charpoly_range_le (I := Fin r) (K := K))

theorem normalizedFactor_mass_le_binary [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (r : ℕ) (g : FixedFreeElement K r) :
    (normalizedFactors (linearUnit K r g.val : Module.End K (Index r → K)).charpoly).card ≤
      r := by
  let A := (linearUnit K r g.val : Module.End K (Index r → K))
  let C := LinearMapPositivePrimaryDecomposition.chart A
  have hsurj : Function.Surjective A := (naturalLinearHom K r g.val).surjective
  have hm := BinaryFixedFreePrimaryDegree.twice_exponent_sum_le_dimension
    hK C hsurj g.property
  have hmass := LinearMapPrimaryWeightedCode.normalizedFactors_card C
  have hd : Module.finrank K (Index r → K) = 2*r := by
    simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_sum,Fintype.card_fin,two_mul]
  rw [hd] at hm
  rw [hmass]
  omega

end SymmetricSubgroupAsymptotics.CFSGSymplecticPrimaryCodeData
