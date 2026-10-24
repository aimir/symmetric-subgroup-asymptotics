import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryPolarCoordinates
import SymmetricSubgroupAsymptotics.QuadraticIsometrySymplecticClassComparison
import SymmetricSubgroupAsymptotics.CFSGSymplecticSmallClassBounds
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCharTwo
import SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupIndexBound

/-! The actual split eight-dimensional quadratic isometry group is
bounded by the actual native symplectic group plus its actual point
stabilizer. The checked original elementary/full-isometry index and
literal central quotient then bound the SAME projective D model.
No subgroup class-count monotonicity or class table is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryIsometryClassBound
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexSingularComponents
open CFSGOrthogonalDIsometryIndexComponents CFSGOrthogonalDBinaryPolarCoordinates
variable (K : Type) [Field K] [Finite K] [CharP K 2]

local instance finiteLinear (r : ℕ) : Finite ((Index r → K) ≃ₗ[K] (Index r → K)) :=
  Finite.of_injective (fun T : (Index r → K) ≃ₗ[K] (Index r → K) =>
    (T : (Index r → K) → (Index r → K))) LinearEquiv.coe_injective

local instance finiteQuadratic (r : ℕ) : Finite (quadraticPreserving K r) :=
  Finite.of_injective (fun g : quadraticPreserving K r => (g.val : Mat K r))
    (by intro g h he; exact Subtype.ext (Units.ext he))

local instance finiteElementary (r : ℕ) : Finite (elementaryRootGroup K r) :=
  Finite.of_injective (fun g : elementaryRootGroup K r => (g.val : Mat K r))
    (by intro g h he; exact Subtype.ext (Units.ext he))

theorem full_class_card_le (hK : Nat.card K = 2) :
    Nat.card (ConjClasses (isometryGroup (splitQuadraticForm K 4))) ≤ 768 := by
  have hE (x y : Index 4 → K) :
      CFSGSymplecticNaturalBilinearClassGeometry.naturalPairing K 4 x y =
        (splitQuadraticForm K 4).polarBilin x y := by
    rw [polar_eq_naturalPairing K 4]
  have h := QuadraticIsometrySymplecticClassComparison.class_card_le K hK 3
    (splitQuadraticForm K 4) (splitQuadraticForm_nondegenerate K 4)
    (LinearEquiv.refl K (Index 4 → K)) hE
  exact h.trans (CFSGSymplecticSmallClassBounds.binary_rankFour_add_point K hK)

theorem quadratic_matrix_class_card_le (hK : Nat.card K = 2) :
    Nat.card (ConjClasses (quadraticPreserving K 4)) ≤ 768 := by
  let e := quadraticIsometryEquiv K 4
  have h := Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
    (ConjClasses.map_surjective e.symm.surjective)
  exact h.trans (full_class_card_le K hK)

theorem elementary_class_card_le (hK : Nat.card K = 2) :
    Nat.card (ConjClasses (elementaryRootGroup K 4)) ≤ 1536 := by
  let S := (elementaryRootGroup K 4).subgroupOf (quadraticPreserving K 4)
  let e := Subgroup.subgroupOfEquivOfLe (elementary_le_quadraticPreserving K 0)
  have hroot : Nat.card (ConjClasses (elementaryRootGroup K 4)) ≤ Nat.card (ConjClasses S) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
      (ConjClasses.map_surjective e.surjective)
  have hS := ConjugacyClassSubgroupIndexBound.class_card_le_index_mul S
  have hidx : S.index ≤ 2 :=
    CFSGOrthogonalDIsometryIndexCharTwo.elementary_quadratic_isometry_index_le_two K 0
  exact hroot.trans (hS.trans ((Nat.mul_le_mul hidx
    (quadratic_matrix_class_card_le K hK)).trans_eq (by decide : 2*768 = 1536)))

theorem projective_class_card_le (hK : Nat.card K = 2) :
    Nat.card (ConjClasses (elementaryProjective K 4)) ≤ 1536 := by
  let f := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K 4))
  have h := Nat.card_le_card_of_surjective (ConjClasses.map f)
    (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))
  exact h.trans (elementary_class_card_le K hK)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryIsometryClassBound
