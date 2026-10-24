import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSourceWordWeights
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalOppositionCoordinates

/-! Exact root-image coordinates from unit lowering and rational weights.
The functionals use only signed simple coordinates and iterated actual
matrix adjoints, with integral coefficients. Their crosszeros are proved
overQ, to be reflected to integers before reduction to any field. No
source-basis or representation-faithfulness assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootCoordinateOrthogonality
open CFSG.Models.Chevalley CFSGFFourSerreMatrices
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalRootFamilyProfile
open CFSGFFourOriginalUnitLoweringPaths CFSGFFourOriginalSourceWordWeights
open CFSGFFourOriginalSeparatingCartan CFSGFFourOriginalOppositionCoordinates
open CFSGRationalLieWeightCoordinates CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _
local notation "A" => CartanMatrix.F₄

def matrixWord (neg:Bool) : List (Fin 4)→Module.End ℚ Mat
  | []=>1
  | i::ss=>matrixWord neg ss*LieAlgebra.ad ℚ Mat (rationalRepresentation (rootVector A neg i))

theorem word_intertwines (neg:Bool) (ss:List (Fin 4)) (x:RationalLie A) :
    matrixWord neg ss (rationalRepresentation x)=rationalRepresentation (wordOperator neg ss x) := by
  induction ss generalizing x with
  | nil=>rfl
  | cons i ss ih=>
    change matrixWord neg ss
      ⁅rationalRepresentation (rootVector A neg i),rationalRepresentation x⁆=
      rationalRepresentation (wordOperator neg ss ⁅rootVector A neg i,x⁆)
    rw [←LieHom.map_lie,ih]

theorem signed_coordinate_weight (neg:Bool) (i:Fin 4) (M:Mat) :
    signedCoordinate neg i ⁅rationalRepresentation testCartan,M⁆=
      (signedTestWeight neg (simpleIndex i):ℚ)*signedCoordinate neg i M := by
  have h:=signed_testCartan_coordinate neg i M
  cases neg
  · exact h
  · simpa only [signedTestWeight,if_true,Int.cast_neg] using h

def rootCoordinate (neg:Bool) (j:Fin 24) : Mat→ₗ[ℚ]ℚ :=
  (pathCoefficient j:ℚ) • (signedCoordinate neg (terminalNode j)).comp
    (matrixWord (!neg) (loweringSteps j))

theorem root_coordinate_self (neg:Bool) (j:Fin 24) :
    rootCoordinate neg j (rationalRepresentation (rootVectors neg j).val)=1 := by
  change (pathCoefficient j:ℚ) • signedCoordinate neg (terminalNode j)
    (matrixWord (!neg) (loweringSteps j) (rationalRepresentation (rootVectors neg j).val))=1
  rw [word_intertwines,unit_lowering,map_smul,map_smul,signed_unit]
  rcases pathCoefficient_unit j with h|h <;> norm_num [h]

theorem root_coordinate_zero (neg:Bool) (j:Fin 24) (k:BasisIndex) (hk:k≠.inl (neg,j)) :
    rootCoordinate neg j (rationalRepresentation (vectors k))=0 := by
  have hs:=word_weight (!neg) (loweringSteps j) (vectors k) (fullWeight k:ℚ)
    (CFSGFFourOriginalSourceWordWeights.family_weight k)
  have hm:⁅rationalRepresentation testCartan,
      matrixWord (!neg) (loweringSteps j) (rationalRepresentation (vectors k))⁆=
      ((fullWeight k:ℚ)+(wordShift (!neg) (loweringSteps j):ℚ)) •
        matrixWord (!neg) (loweringSteps j) (rationalRepresentation (vectors k)) := by
    simpa only [word_intertwines,LieHom.map_lie,map_smul] using congrArg rationalRepresentation hs
  have hne:(fullWeight k:ℚ)+(wordShift (!neg) (loweringSteps j):ℚ)≠
      (signedTestWeight neg (simpleIndex (terminalNode j)):ℚ) := by
    intro he
    have he':((fullWeight k+wordShift (!neg) (loweringSteps j):ℤ):ℚ)=
        (signedTestWeight neg (simpleIndex (terminalNode j)):ℚ) := by
      simpa only [Int.cast_add] using he
    have hz:=Int.cast_injective he'
    have hb:=lowering_weight_balance neg j
    have hsame:fullWeight k=signedTestWeight neg j:=by omega
    exact hk ((fullWeight_eq_root_iff neg j k).mp hsame)
  have hz:=coordinate_zero_of_weights_ne (rationalRepresentation testCartan)
    (signedCoordinate neg (terminalNode j))
    ((fullWeight k:ℚ)+(wordShift (!neg) (loweringSteps j):ℚ))
    (signedTestWeight neg (simpleIndex (terminalNode j)):ℚ)
    (signed_coordinate_weight neg (terminalNode j))
    (matrixWord (!neg) (loweringSteps j) (rationalRepresentation (vectors k))) hm hne
  change (pathCoefficient j:ℚ) • signedCoordinate neg (terminalNode j)
    (matrixWord (!neg) (loweringSteps j) (rationalRepresentation (vectors k)))=0
  rw [hz,smul_zero]

theorem root_coordinate_vector (neg:Bool) (j:Fin 24) (k:BasisIndex) :
    rootCoordinate neg j (rationalRepresentation (vectors k))=if k=.inl (neg,j) then 1 else 0 := by
  by_cases hk:k=.inl (neg,j)
  · subst k
    rw [if_pos rfl]
    exact root_coordinate_self neg j
  · rw [if_neg hk]
    exact root_coordinate_zero neg j k hk

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootCoordinateOrthogonality
