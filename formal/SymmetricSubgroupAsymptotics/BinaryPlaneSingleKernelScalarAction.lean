import SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelCubic
import SymmetricSubgroupAsymptotics.BinaryPlaneCubicScalarChart
import SymmetricSubgroupAsymptotics.BinaryCubicScalarLinearRepresentation
import Mathlib.GroupTheory.Index

/-! Honest scalar coordinates for the centralizer of the actual common
cubic subgroup. The larger original group is not asserted scalar-linear. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelScalarAction
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)
open BinaryQuadraticField (Scalar omega)

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I]
    (C : Subgroup (W (R := R) (I := I))) (i₀ : I)
    (hsingle : ∀ i : I, localKernel C i = localKernel C i₀)
    (hO : oddKernel C ≠ ⊥)

abbrev centralizer : Subgroup C := (MulAut.conjNormal : C →* MulAut (oddKernel C)).ker

include hsingle hO in
/-- The actual centralizer has index at most two by its action on actual O. -/
theorem centralizer_index_le_two : (centralizer C).index ≤ 2 := by
  letI : Finite (MulAut (oddKernel C)) := Finite.of_injective
    (fun f : MulAut (oddKernel C) => (fun x => f x)) DFunLike.coe_injective
  rw [Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective
    (MulAut.conjNormal : C →* MulAut (oddKernel C)).range.subtype Subtype.val_injective).trans
      (RankOneCubicSylowCentralizer.automorphism_card_le_two
        (BinaryPlaneSingleKernelCubic.cubicEquiv C i₀ hsingle hO))

abbrev actualGenerator : oddKernel C := BinaryPlaneSingleKernelCubic.generator C i₀ hsingle hO

/-- O is abelian, so its actual generator belongs to this actual centralizer. -/
def scalarGenerator : centralizer C :=
  ⟨(actualGenerator C i₀ hsingle hO : C),by
    apply MulEquiv.ext
    intro o
    apply Subtype.ext
    let k := actualGenerator C i₀ hsingle hO
    have hm : (k : C)*(o : C) = (o : C)*(k : C) :=
      congrArg (fun z : oddKernel C => (z : C))
        (isMulCommutative_iff.mp (commutative C) k o)
    change (k : C)*(o : C)*(k : C)⁻¹ = (o : C)
    rw [hm,mul_assoc,mul_inv_cancel,mul_one]⟩

theorem centralizes_generator (h : centralizer C) :
    Commute h (scalarGenerator C i₀ hsingle hO) := by
  have ha : (MulAut.conjNormal : C →* MulAut (oddKernel C)) (h : C) = 1 := h.property
  have hh := congrArg (fun f : MulAut (oddKernel C) =>
    (f (actualGenerator C i₀ hsingle hO) : C)) ha
  change (h : C)*(actualGenerator C i₀ hsingle hO : C)*(h : C)⁻¹ =
    (actualGenerator C i₀ hsingle hO : C) at hh
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- Each local chart is certified by its own actual cubic operator. -/
def coordinateChart (i : I) : Plane ≃ₗ[ZMod 2] Scalar :=
  Classical.choose (BinaryPlaneCubicScalarChart.exists_chart
    (localLinear C i (actualGenerator C i₀ hsingle hO))
    (local_cubic C i (actualGenerator C i₀ hsingle hO))
    (BinaryPlaneSingleKernelCubic.generator_local_fixedFree C i₀ hsingle hO i))

theorem coordinateChart_action (i : I) (v : Plane) :
    coordinateChart C i₀ hsingle hO i
        (localLinear C i (actualGenerator C i₀ hsingle hO) v) =
      omega * coordinateChart C i₀ hsingle hO i v :=
  Classical.choose_spec (BinaryPlaneCubicScalarChart.exists_chart
    (localLinear C i (actualGenerator C i₀ hsingle hO))
    (local_cubic C i (actualGenerator C i₀ hsingle hO))
    (BinaryPlaneSingleKernelCubic.generator_local_fixedFree C i₀ hsingle hO i)) v

def functionChart : (I → Plane) ≃ₗ[ZMod 2] (I → Scalar) :=
  LinearEquiv.piCongrRight (coordinateChart C i₀ hsingle hO)

def binaryRepresentation : Representation (ZMod 2) (centralizer C) (I → Scalar) :=
  (functionChart C i₀ hsingle hO).conjRingEquiv.toMonoidHom.comp
    ((BinaryPlaneCyclicWreathUniform.representation C).comp (centralizer C).subtype)

/-- Omega is the action of the displayed actual group element. -/
theorem scalarGenerator_action (v : I → Scalar) :
    binaryRepresentation C i₀ hsingle hO (scalarGenerator C i₀ hsingle hO) v = omega • v := by
  funext i
  change coordinateChart C i₀ hsingle hO i
    (localLinear C i (actualGenerator C i₀ hsingle hO)
      ((functionChart C i₀ hsingle hO).symm v
        ((((actualGenerator C i₀ hsingle hO : oddKernel C) : C) : W (R := R) (I := I)).right⁻¹ • i))) =
      omega * v i
  rw [top_one C,inv_one,one_smul,coordinateChart_action]
  change omega * coordinateChart C i₀ hsingle hO i
    ((coordinateChart C i₀ hsingle hO i).symm (v i)) = omega * v i
  rw [LinearEquiv.apply_symm_apply]

/-- Only operators of the actual cubic centralizer are upgraded to F4. -/
def scalarRepresentation : Representation Scalar (centralizer C) (I → Scalar) :=
  BinaryCubicScalarLinearRepresentation.representation
    (binaryRepresentation C i₀ hsingle hO) (scalarGenerator C i₀ hsingle hO)
    (scalarGenerator_action C i₀ hsingle hO) (centralizes_generator C i₀ hsingle hO)

theorem scalarRepresentation_apply (h : centralizer C) (v : I → Scalar) :
    scalarRepresentation C i₀ hsingle hO h v = binaryRepresentation C i₀ hsingle hO h v := rfl

end SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelScalarAction
