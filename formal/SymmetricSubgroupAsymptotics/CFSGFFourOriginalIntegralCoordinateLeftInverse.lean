import SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralCartanCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralSpan

/-! An actual integral left inverse for the SAME original F4 Serre
representation. Primitive root and Cartan coordinates give Kronecker
values on all52 vectors; exact original lattice spanning then proves
the left-inverse identity on every lattice element. No rational-dimension
argument, ordinary F4 simplicity or tensor-faithfulness premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralCoordinateLeftInverse
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGFFourSerreMatrices
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalIntegralSpan
open CFSGFFourOriginalIntegralRootCoordinates CFSGFFourOriginalIntegralCartanCoordinates
open CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _
local notation "A" => CartanMatrix.F₄

def matrixCoordinates : IntMat→ₗ[ℤ](BasisIndex→ℤ) where
  toFun M k:=match k with
    | .inl (neg,j)=>integerRootCoordinate neg j M
    | .inr b=>integerCartanCoordinate b M
  map_add' M N:=by
    funext k
    cases k with
    | inl z=>exact map_add (integerRootCoordinate z.1 z.2) M N
    | inr b=>exact map_add (integerCartanCoordinate b) M N
  map_smul' c M:=by
    funext k
    cases k with
    | inl z=>exact map_smul (integerRootCoordinate z.1 z.2) c M
    | inr b=>exact map_smul (integerCartanCoordinate b) c M

theorem matrixCoordinates_vector (k:BasisIndex) :
    matrixCoordinates (integralRepresentation realizationData (integralVectors k))=Pi.single k 1 := by
  funext j
  cases j with
  | inl z=>
    change integerRootCoordinate z.1 z.2
      (integralRepresentation realizationData (integralVectors k))=(Pi.single k 1 : BasisIndex→ℤ) (.inl z)
    rw [CFSGFFourOriginalIntegralRootCoordinates.coordinate_integral_vector,Pi.single_apply]
    simp only [Prod.mk.eta,eq_comm]
  | inr b=>
    change integerCartanCoordinate b
      (integralRepresentation realizationData (integralVectors k))=(Pi.single k 1 : BasisIndex→ℤ) (.inr b)
    rw [CFSGFFourOriginalIntegralCartanCoordinates.coordinate_integral_vector,Pi.single_apply]
    simp only [eq_comm]

def integralCoordinates : integralLattice A→ₗ[ℤ](BasisIndex→ℤ) :=
  matrixCoordinates.comp (integralRepresentation realizationData)

def integralCombination : (BasisIndex→ℤ)→ₗ[ℤ]integralLattice A :=
  Fintype.linearCombination ℤ integralVectors

theorem integralCoordinates_vector (k:BasisIndex) :
    integralCoordinates (integralVectors k)=Pi.single k 1 := matrixCoordinates_vector k

theorem integralCoordinates_combination (a:BasisIndex→ℤ) :
    integralCoordinates (integralCombination a)=a := by
  change integralCoordinates (∑k,a k • integralVectors k)=a
  rw [map_sum]
  simp only [map_smul,integralCoordinates_vector]
  funext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem integralCombination_val (a:BasisIndex→ℤ) :
    (integralCombination a).val=∑k,a k • vectors k := by
  change (integralLattice A).subtype (∑k,a k • integralVectors k)=∑k,a k • vectors k
  simp only [map_sum,map_smul,Submodule.subtype_apply,vectors]

theorem integralCombination_surjective : Function.Surjective integralCombination := by
  intro x
  have hspan:integralLattice A=Submodule.span ℤ (Set.range vectors):=
    original_integralLattice_eq_span
  have hx:x.val∈Submodule.span ℤ (Set.range vectors) := by
    rw [←hspan]
    exact x.property
  obtain ⟨a,ha⟩:=(Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  refine ⟨a,Subtype.ext ?_⟩
  exact (integralCombination_val a).trans ha

theorem integralCombination_coordinates (x:integralLattice A) :
    integralCombination (integralCoordinates x)=x := by
  obtain ⟨a,rfl⟩:=integralCombination_surjective x
  rw [integralCoordinates_combination]

def integralLeftInverse : IntMat→ₗ[ℤ]integralLattice A := integralCombination.comp matrixCoordinates

theorem integralRepresentation_leftInverse :
    Function.LeftInverse integralLeftInverse (integralRepresentation realizationData) :=
  integralCombination_coordinates

theorem integralRepresentation_injective : Function.Injective (integralRepresentation realizationData) :=
  integralRepresentation_leftInverse.injective

def integralBasisEquiv : integralLattice A≃ₗ[ℤ](BasisIndex→ℤ) where
  __:=integralCoordinates
  invFun:=integralCombination
  left_inv:=integralCombination_coordinates
  right_inv:=integralCoordinates_combination

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralCoordinateLeftInverse
