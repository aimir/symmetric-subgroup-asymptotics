import SymmetricSubgroupAsymptotics.BinaryCoordinateBasisChecks
import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50

/-!
# Literal coordinates and algebra operators for joint row 17

The ternary blocks, in cyclic order, are (3,7,11), (6,10,2),
(9,1,5), (0,4,8). On their two-dimensional augmentations write
R(a,b)=(a+b,a) and F(a,b)=(b,a). The two four-dimensional copies are
(a,b,Fa,Fb) and its global R-multiple. The eight columns below retain
these copies in alternating column order.

For the original generators g,s, put P=g+g² and Q=P(g+s²)P.
The sixteen elements s^i Q s^-j act as row matrix units on the two
copies. The actual algebra element (1+g+g²)(1+h+h²), h=sgs^-1,
projects onto the four block-constant coordinates. All finite checks
below concern displayed basis vectors and individual points only.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow17NaturalCoordinates

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev Top := Row17Top
abbrev Vector := Fin 12 → ZMod 2
abbrev Rect := Fin 4 → Fin 2 → ZMod 2

def generators : Fin 2 → Top := closureGenerators row17Generators

theorem generators_full : Subgroup.closure (Set.range generators) = ⊤ :=
  closureGenerators_full row17Generators

def g : Top := generators 0
def s : Top := generators 1
def h : Top := s * g * s⁻¹

def representation : Representation (ZMod 2) Top Vector :=
  permutationFunctionRepresentation (ZMod 2) Top (Fin 12)

def constantBasis : Fin 4 → ℕ := ![2184, 1092, 546, 273]
def augmentationBasis : Fin 8 → ℕ :=
  ![2090, 680, 340, 1345, 2720, 2570, 1285, 85]
def augmentationDual : Fin 8 → ℕ :=
  ![2570, 2720, 85, 1285, 680, 2090, 1345, 340]

def constantChart : BinaryCoordinateSpace 12 4 :=
  binaryCoordinateSpaceOfBasisMasks 12 4 constantBasis constantBasis (by
    intro i
    funext j
    revert i j
    decide +kernel)

def augmentationChart : BinaryCoordinateSpace 12 8 :=
  binaryCoordinateSpaceOfBasisMasks 12 8 augmentationBasis augmentationDual (by
    intro i
    funext j
    revert i j
    decide +kernel)

private theorem constant_positive : ∀ q j x,
    constantChart.inclusion (constantChart.coordinates
      (representation (generators q) (constantChart.inclusion (Pi.single j 1)))) x =
      representation (generators q) (constantChart.inclusion (Pi.single j 1)) x := by
  decide +kernel

private theorem constant_negative : ∀ q j x,
    constantChart.inclusion (constantChart.coordinates
      (representation (generators q)⁻¹ (constantChart.inclusion (Pi.single j 1)))) x =
      representation (generators q)⁻¹ (constantChart.inclusion (Pi.single j 1)) x := by
  decide +kernel

private theorem augmentation_positive : ∀ q j x,
    augmentationChart.inclusion (augmentationChart.coordinates
      (representation (generators q) (augmentationChart.inclusion (Pi.single j 1)))) x =
      representation (generators q) (augmentationChart.inclusion (Pi.single j 1)) x := by
  decide +kernel

private theorem augmentation_negative : ∀ q j x,
    augmentationChart.inclusion (augmentationChart.coordinates
      (representation (generators q)⁻¹ (augmentationChart.inclusion (Pi.single j 1)))) x =
      representation (generators q)⁻¹ (augmentationChart.inclusion (Pi.single j 1)) x := by
  decide +kernel

def constants : Subrepresentation representation :=
  constantChart.subrepresentationOfGenerators representation generators generators_full
    (fun q j ↦ (constantChart.mem_iff _).mpr (funext (constant_positive q j)))
    (fun q j ↦ (constantChart.mem_iff _).mpr (funext (constant_negative q j)))

def augmentation : Subrepresentation representation :=
  augmentationChart.subrepresentationOfGenerators representation generators generators_full
    (fun q j ↦ (augmentationChart.mem_iff _).mpr (funext (augmentation_positive q j)))
    (fun q j ↦ (augmentationChart.mem_iff _).mpr (funext (augmentation_negative q j)))

def rectangleIndex : Fin 4 × Fin 2 ≃ Fin 8 := finProdFinEquiv

def rectangularCoordinates : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] Rect where
  toFun v i j := v (rectangleIndex (i, j))
  invFun v t := v (rectangleIndex.symm t).1 (rectangleIndex.symm t).2
  left_inv v := by
    funext t
    exact congrArg v (rectangleIndex.apply_symm_apply t)
  right_inv v := by
    funext i j
    change v (rectangleIndex.symm (rectangleIndex (i, j))).1
      (rectangleIndex.symm (rectangleIndex (i, j))).2 = v i j
    rw [rectangleIndex.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rowUnit (i j : Fin 4) : Module.End (ZMod 2) (Fin 8 → ZMod 2) :=
  rectangularCoordinates.symm.toLinearMap.comp
    ((LinearMap.single (ZMod 2) (fun _ : Fin 4 ↦ Fin 2 → ZMod 2) i).comp
      ((LinearMap.proj j).comp rectangularCoordinates.toLinearMap))

def firstOperator : Module.End (ZMod 2) Vector :=
  representation g + representation g ^ 2

def cornerOperator : Module.End (ZMod 2) Vector :=
  firstOperator * (representation g + representation s ^ 2) * firstOperator

def unitOperator (i j : Fin 4) : Module.End (ZMod 2) Vector :=
  representation (s ^ i.val) * cornerOperator * representation ((s⁻¹) ^ j.val)

def cornerScalar : (ZMod 2)[Top] :=
  (MonoidAlgebra.single g 1 + MonoidAlgebra.single g 1 ^ 2) *
    (MonoidAlgebra.single g 1 + MonoidAlgebra.single s 1 ^ 2) *
    (MonoidAlgebra.single g 1 + MonoidAlgebra.single g 1 ^ 2)

def unitScalar (i j : Fin 4) : (ZMod 2)[Top] :=
  MonoidAlgebra.single (s ^ i.val) 1 * cornerScalar *
    MonoidAlgebra.single ((s⁻¹) ^ j.val) 1

theorem unitOperator_eq (i j : Fin 4) :
    unitOperator i j = representation.asAlgebraHom (unitScalar i j) := by
  simp only [unitOperator, cornerOperator, firstOperator, unitScalar, cornerScalar,
    map_mul, map_add, map_pow, Representation.asAlgebraHom_single, one_smul]

private theorem unit_basis_checked : ∀ (i j : Fin 4) (t : Fin 8) (x : Fin 12),
    unitOperator i j (augmentationChart.inclusion (Pi.single t 1)) x =
      augmentationChart.inclusion (rowUnit i j (Pi.single t 1)) x := by
  decide +kernel

theorem unit_apply (i j : Fin 4) (v : Fin 8 → ZMod 2) :
    unitOperator i j (augmentationChart.inclusion v) =
      augmentationChart.inclusion (rowUnit i j v) := by
  have hm : (unitOperator i j).comp augmentationChart.inclusion =
      augmentationChart.inclusion.comp (rowUnit i j) := by
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro t
    rw [Pi.basisFun_apply]
    exact funext (unit_basis_checked i j t)
  exact LinearMap.congr_fun hm v

def projectionOperator : Module.End (ZMod 2) Vector :=
  (1 + representation g + representation g ^ 2) *
    (1 + representation h + representation h ^ 2)

def projectionScalar : (ZMod 2)[Top] :=
  (1 + MonoidAlgebra.single g 1 + MonoidAlgebra.single g 1 ^ 2) *
    (1 + MonoidAlgebra.single h 1 + MonoidAlgebra.single h 1 ^ 2)

theorem projectionOperator_eq :
    projectionOperator = representation.asAlgebraHom projectionScalar := by
  simp only [projectionOperator, projectionScalar, map_mul, map_add, map_pow, map_one,
    Representation.asAlgebraHom_single, one_smul]

private theorem projection_constant_basis : ∀ (i : Fin 4) (x : Fin 12),
    projectionOperator (constantChart.inclusion (Pi.single i 1)) x =
      constantChart.inclusion (Pi.single i 1) x := by
  decide +kernel

private theorem projection_augmentation_basis : ∀ (i : Fin 8) (x : Fin 12),
    projectionOperator (augmentationChart.inclusion (Pi.single i 1)) x = 0 := by
  decide +kernel

theorem projection_constant (v : Fin 4 → ZMod 2) :
    projectionOperator (constantChart.inclusion v) = constantChart.inclusion v := by
  have hm : projectionOperator.comp constantChart.inclusion = constantChart.inclusion := by
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (projection_constant_basis i)
  exact LinearMap.congr_fun hm v

theorem projection_augmentation (v : Fin 8 → ZMod 2) :
    projectionOperator (augmentationChart.inclusion v) = 0 := by
  have hm : projectionOperator.comp augmentationChart.inclusion = 0 := by
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (projection_augmentation_basis i)
  exact LinearMap.congr_fun hm v

private theorem decomposition_basis : ∀ (i x : Fin 12),
    (constantChart.inclusion.comp constantChart.coordinates +
      augmentationChart.inclusion.comp augmentationChart.coordinates)
        (Pi.single i 1) x = (Pi.single i 1 : Vector) x := by
  decide +kernel

theorem decomposition (v : Vector) :
    constantChart.inclusion (constantChart.coordinates v) +
      augmentationChart.inclusion (augmentationChart.coordinates v) = v := by
  have hm : constantChart.inclusion.comp constantChart.coordinates +
      augmentationChart.inclusion.comp augmentationChart.coordinates = LinearMap.id := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (decomposition_basis i)
  exact LinearMap.congr_fun hm v

private theorem constant_orbit_basis : ∀ (i : Fin 4) (x : Fin 12),
    representation (s ^ i.val) (constantChart.inclusion (Pi.single 0 1)) x =
      constantChart.inclusion (Pi.single i 1) x := by
  decide +kernel

theorem constant_orbit (i : Fin 4) :
    representation (s ^ i.val) (constantChart.inclusion (Pi.single 0 1)) =
      constantChart.inclusion (Pi.single i 1) :=
  funext (constant_orbit_basis i)

end PrimitiveAffineDegreeTwoTwelveRow17NaturalCoordinates
end SymmetricSubgroupAsymptotics

end
