import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramMatrices
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootReindex
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramFree

/-! Diagram covariance of the SAME integral coordinate Geck realization.
The integer generators follow by cast injectivity from actual rational
matrix covariance. The integer second coefficients follow from their
proved square identities; no characteristic restriction is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIntegral
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateDiagramIndices CFSGNormTwoCoordinateDiagramMatrices
open CFSGQuadraticRootReindex CFSGSerreQuadraticMatrix
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
    (p : Equiv.Perm (Fin r)) (hA : ∀ i j,A (p i) (p j)=A i j)

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "σ" => combinedIndex A hd hs hp ho p hA

include hA in
theorem source_cartan_preserved (i j : Fin r) :
    CFSGGeckSerreRepresentation.cartan b₀ s₀ (p i) (p j)=
      CFSGGeckSerreRepresentation.cartan b₀ s₀ i j := by
  simp only [CFSGGeckSerreRepresentation.cartan,coordinate_cartan]
  exact hA j i

theorem integerGenerator_covariance (g : CartanMatrix.Generators (Fin r)) :
    Matrix.reindexAlgEquiv ℤ ℤ σ ((D).integerGenerator g)=
      (D).integerGenerator (CFSGSerreDiagram.nodeRename p g) := by
  apply integer_eq_of_rational σ
  cases g with
  | H i=>
    change Matrix.reindexAlgEquiv ℚ ℚ σ
      ((Int.castRingHom ℚ).mapMatrix (CFSGGeckIntegralMatrices.H b₀ (s₀ i)))=
        (Int.castRingHom ℚ).mapMatrix (CFSGGeckIntegralMatrices.H b₀ (s₀ (p i)))
    rw [CFSGGeckIntegralMatrices.map_H,CFSGGeckIntegralMatrices.map_H]
    change algebraEquiv A hd hs hp ho p hA (RootPairing.GeckConstruction.h (s₀ i))=_
    rw [algebraEquiv_H,supportPermutation_simple]
  | E i=>
    change Matrix.reindexAlgEquiv ℚ ℚ σ
      ((Int.castRingHom ℚ).mapMatrix (CFSGGeckIntegralMatrices.E b₀ (s₀ i)))=
        (Int.castRingHom ℚ).mapMatrix (CFSGGeckIntegralMatrices.E b₀ (s₀ (p i)))
    rw [CFSGGeckIntegralMatrices.map_E,CFSGGeckIntegralMatrices.map_E]
    change algebraEquiv A hd hs hp ho p hA (RootPairing.GeckConstruction.e (s₀ i))=_
    rw [algebraEquiv_E,supportPermutation_simple]
  | F i=>
    change Matrix.reindexAlgEquiv ℚ ℚ σ
      ((Int.castRingHom ℚ).mapMatrix (CFSGGeckIntegralMatrices.F b₀ (s₀ i)))=
        (Int.castRingHom ℚ).mapMatrix (CFSGGeckIntegralMatrices.F b₀ (s₀ (p i)))
    rw [CFSGGeckIntegralMatrices.map_F,CFSGGeckIntegralMatrices.map_F]
    change algebraEquiv A hd hs hp ho p hA (RootPairing.GeckConstruction.f (s₀ i))=_
    rw [algebraEquiv_F,supportPermutation_simple]

theorem integerRoot_covariance (neg : Bool) (i : Fin r) :
    Matrix.reindexAlgEquiv ℤ ℤ σ (integerRoot D neg i)=integerRoot D neg (p i) := by
  cases neg
  · exact integerGenerator_covariance A hd hs hp ho p hA (.E i)
  · exact integerGenerator_covariance A hd hs hp ho p hA (.F i)

theorem integerSecond_covariance (neg : Bool) (i : Fin r) :
    Matrix.reindexAlgEquiv ℤ ℤ σ ((D).integerSecond neg i)=(D).integerSecond neg (p i) :=
  integerSecond_reindex D σ p (integerRoot_covariance A hd hs hp ho p hA) neg i

theorem fieldRoot_covariance (K : Type*) [CommRing K] (neg : Bool) (i : Fin r) :
    Matrix.reindexAlgEquiv K K σ (fieldRoot D K neg i)=fieldRoot D K neg (p i) :=
  fieldRoot_reindex D σ p (integerRoot_covariance A hd hs hp ho p hA) K neg i

theorem fieldSecond_covariance (K : Type*) [CommRing K] (neg : Bool) (i : Fin r) :
    Matrix.reindexAlgEquiv K K σ (fieldSecond D K neg i)=fieldSecond D K neg (p i) :=
  fieldSecond_reindex D σ p (integerRoot_covariance A hd hs hp ho p hA) K neg i

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIntegral
