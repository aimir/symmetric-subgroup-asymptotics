import SymmetricSubgroupAsymptotics.BinaryPlaneTwoClassSignNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryPlaneTwoClassOddNormalGenerators
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration

/-! Two inherited abelian layers of the SAME native linear image cost two
ordinary generators above its actual block top. The actual odd-coordinate
kernel classes, their transporter, and both actual quotient maps are kept. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneTwoClassOrdinaryGenerators
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)
open BinaryPlaneActualSignKernelCoordinates

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I] (C : Subgroup (W (R := R) (I := I)))

theorem signKernel_commutative : IsMulCommutative (Kernel C) := by
  apply IsMulCommutative.of_comm
  intro u v
  apply coordinate_joint_injective C
  funext i
  change coordinate C i (u*v) = coordinate C i (v*u)
  rw [map_mul,map_mul,mul_comm]

theorem genRank_le_top_add_two
    (htop : Function.Surjective (PermutationalWreathProduct.rightHom.comp C.subtype))
    (htrans : ∀ i j : I, ∃ h : C, (h : W (R := R) (I := I)).right • i = j)
    (hO : oddKernel C ≠ ⊥) (i j : I) (hne : localKernel C i ≠ localKernel C j)
    (hcover : ∀ k : I, localKernel C k = localKernel C i ∨ localKernel C k = localKernel C j) :
    MarkedC4.genRank C ≤ MarkedC4.genRank R + 2 := by
  let f : C →* Image C := (signProjection C).rangeRestrict
  letI : Finite (Image C) := Finite.of_surjective f (signProjection C).rangeRestrict_surjective
  letI : IsMulCommutative (oddKernel C) := commutative C
  letI : IsMulCommutative f.ker := by
    change IsMulCommutative (signProjection C).rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hodd : MarkedC4.normalGen f.ker ≤ 1 := by
    change MarkedC4.normalGen (signProjection C).rangeRestrict.ker ≤ 1
    rw [MonoidHom.ker_rangeRestrict]
    exact BinaryPlaneTwoClassOddNormalGenerators.normalGen_le_one_of_two_classes
      C htrans i j hne hcover
  have hfirst := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    f (signProjection C).rangeRestrict_surjective
  letI : IsMulCommutative (top C).ker := signKernel_commutative C
  have hsign := BinaryPlaneTwoClassSignNormalGenerators.normalGen_le_one_of_two_classes
    C htrans hO i j hne hcover
  change MarkedC4.normalGen (top C).ker ≤ 1 at hsign
  have hsurj : Function.Surjective (top C) := by
    intro r
    obtain ⟨h,hh⟩ := htop r
    refine ⟨f h,?_⟩
    exact hh
  have hsecond := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (top C) hsurj
  omega

end SymmetricSubgroupAsymptotics.BinaryPlaneTwoClassOrdinaryGenerators
