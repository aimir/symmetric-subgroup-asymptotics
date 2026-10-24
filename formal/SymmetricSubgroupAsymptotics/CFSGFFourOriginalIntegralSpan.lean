import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSignedSourceActions
import SymmetricSubgroupAsymptotics.CFSGSerreIntegralCubicFamilySpan

/-! Exact spanning of the SAME original F4 integral Serre lattice by
the52 displayed divided-power vectors. The signed source table gives
integral first adjoints; its even two-step products and zero three-step
products give integral half-squares and cubic nilpotence. Thus every
original divided power preserves their Z-span, and original lattice
minimality proves equality. Independence and tensor faithfulness are
separate obligations, not consequences assumed in this proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralSpan
open CFSG.Models.Chevalley CFSGSerreIntegralCubicFamilySpan
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalRootFamilyProfile
open CFSGFFourOriginalSignedActionEntries CFSGFFourOriginalSignedSourceActions
local notation "A" => CartanMatrix.F₄

def integralSpan : Submodule ℤ (RationalLie A):=Submodule.span ℤ (Set.range vectors)

theorem vector_mem (j:BasisIndex) : vectors j∈integralSpan :=
  Submodule.subset_span ⟨j,rfl⟩

theorem generator_mem (g:CartanMatrix.Generators (Fin 4)) : generator A g∈integralSpan := by
  cases g with
  | E i=>
    have h:=vector_mem (.inl (false,simpleIndex i))
    change family false (.inl (simpleIndex i))∈integralSpan at h
    rw [simple_value] at h
    exact h
  | F i=>
    have h:=vector_mem (.inl (true,simpleIndex i))
    change family true (.inl (simpleIndex i))∈integralSpan at h
    rw [simple_value] at h
    exact h
  | H i=>exact vector_mem (.inr i)

theorem first_mem (neg:Bool) (i:Fin 4) (j:BasisIndex) :
    ⁅rootVector A neg i,vectors j⁆∈integralSpan := by
  rw [action,Int.cast_smul_eq_zsmul]
  exact integralSpan.smul_mem _ (vector_mem _)

private theorem square_action (neg:Bool) (i:Fin 4) (j:BasisIndex) :
    ((LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i))^2) (vectors j)=
      (((signedEntry neg i j).2*(signedEntry neg i (signedEntry neg i j).1).2:ℤ):ℚ) •
        vectors (signedEntry neg i (signedEntry neg i j).1).1 := by
  change ⁅rootVector A neg i,⁅rootVector A neg i,vectors j⁆⁆=_
  rw [action,lie_smul,action,smul_smul,Int.cast_mul]

def halfSquareVector (neg:Bool) (i:Fin 4) (j:BasisIndex) : RationalLie A :=
  (squareEntry neg i j).2 • vectors (squareEntry neg i j).1

theorem halfSquare_mem (neg:Bool) (i:Fin 4) (j:BasisIndex) :
    halfSquareVector neg i j∈integralSpan := integralSpan.smul_mem _ (vector_mem _)

theorem square_eq_twice_half (neg:Bool) (i:Fin 4) (j:BasisIndex) :
    ((LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i))^2) (vectors j)=
      (2:ℚ) • halfSquareVector neg i j := by
  rw [square_action,second_coefficient_even]
  change ((2*(squareEntry neg i j).2:ℤ):ℚ) • vectors (squareEntry neg i j).1=
    (2:ℚ) • ((squareEntry neg i j).2 • vectors (squareEntry neg i j).1)
  simp only [Int.cast_mul,Int.cast_ofNat,←Int.cast_smul_eq_zsmul ℚ,smul_smul]

theorem cube_zero (neg:Bool) (i:Fin 4) (j:BasisIndex) :
    ((LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i))^3) (vectors j)=0 := by
  have hc:=congrArg (fun z:ℤ=>(z:ℚ)) (third_coefficient_zero neg i j)
  simp only [Int.cast_mul,Int.cast_zero,mul_assoc] at hc
  change ⁅rootVector A neg i,⁅rootVector A neg i,⁅rootVector A neg i,vectors j⁆⁆⁆=0
  rw [action,lie_smul,lie_smul,action,lie_smul,action]
  simp only [smul_smul,mul_assoc,hc,zero_smul]

theorem original_integralLattice_eq_span : integralLattice A=integralSpan :=
  integralLattice_eq_span_of_cubic_family A integralVectors generator_mem first_mem
    (fun neg i j=>⟨halfSquareVector neg i j,halfSquare_mem neg i j,square_eq_twice_half neg i j⟩)
    cube_zero

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralSpan
