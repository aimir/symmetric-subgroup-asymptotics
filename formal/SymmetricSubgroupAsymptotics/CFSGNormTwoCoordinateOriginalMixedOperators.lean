import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMixedImageTransport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAdjointRootOperators
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTripleRootPolynomial
import SymmetricSubgroupAsymptotics.CFSGGeckSerreImage
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedLieInvariance

/-! The original Serre operators for two orthogonal simple roots have
zero mixed second-first, first-second and second-second compositions on
their SAME integral image, in both signs and every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalMixedOperators

theorem mixed_powers_zero {B : Type*} [Ring B] (X Y : B) (hc : Commute X Y)
    (hXY : X^2*Y=0) (hYX : Y^2*X=0) (k l : ℕ)
    (hkl : (k=2∧l=1)∨(k=1∧l=2)∨(k=2∧l=2)) : X^k*Y^l=0 := by
  rcases hkl with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · simpa only [pow_one] using hXY
  · simpa only [pow_one,(hc.pow_right 2).eq] using hYX
  · calc
      X^2*Y^2=(X^2*Y)*Y := by rw [pow_two Y,mul_assoc]
      _=0 := by rw [hXY,zero_mul]

open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckTripleRootPolynomial CFSGNormTwoCoordinateAdjointRootOperators
open CFSGNormTwoGeckGeneratedLieInvariance CFSGSerreQuadraticMatrix
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "C" => CFSGGeckSerreRepresentation.cartan b₀ s₀
local notation "L" => RootPairing.GeckConstruction.lieAlgebra b₀

theorem rational_mixed_ad_zero (neg : Bool) (i j : Fin r)
    (hij : integerPairing A (s₀ i:Roots A).val (s₀ j:Roots A).val=0)
    (k l : ℕ) (hkl : (k=2∧l=1)∨(k=1∧l=2)∨(k=2∧l=2)) (x : RationalLie C) :
    (LieAlgebra.ad ℚ _ (fieldRoot D ℚ neg i)^k)
      ((LieAlgebra.ad ℚ _ (fieldRoot D ℚ neg j)^l) ((D).rational x))=0 := by
  let a := signedSimpleRoot A hs hp b₀ s₀ neg i
  let b := signedSimpleRoot A hs hp b₀ s₀ neg j
  have hab : integerPairing A a.val b.val=0 := signed_orthogonal A hs hp b₀ s₀ neg i j hij
  have hX := root_mem_generated A hs hp b₀ s₀ neg i
  have hY := root_mem_generated A hs hp b₀ s₀ neg j
  have hXa := root_signed_degree A hs hp b₀ s₀ ℚ neg i
  have hYb := root_signed_degree A hs hp b₀ s₀ ℚ neg j
  let X : Module.End ℚ L := rootAdjoint A hd hs hp ho (fieldRoot D ℚ neg i) hX
  let Y : Module.End ℚ L := rootAdjoint A hd hs hp ho (fieldRoot D ℚ neg j) hY
  have hc : Commute X Y := rootAdjoints_commute A hd hs hp ho a b hab _ _ hX hY hXa hYb
  have hXY : X^2*Y=0 := rootAdjoints_mixed_zero A hd hs hp ho a b hab _ _ hX hY hXa hYb
  have hba : integerPairing A b.val a.val=0 := by rw [integer_symmetric A hs];exact hab
  have hYX : Y^2*X=0 := rootAdjoints_mixed_zero A hd hs hp ho b a hba _ _ hY hX hYb hXa
  have hz := mixed_powers_zero X Y hc hXY hYX k l hkl
  let M : L := ⟨(D).rational x,CFSGGeckSerreImage.rationalRepresentation_mem_lieAlgebra b₀ s₀ x⟩
  rcases hkl with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals exact congrArg (fun f : Module.End ℚ L=>(f M).val) hz

theorem integral_original_mixed_zero (neg : Bool) (i j : Fin r)
    (hij : integerPairing A (s₀ i:Roots A).val (s₀ j:Roots A).val=0)
    (k l : ℕ) (hkl : (k=2∧l=1)∨(k=1∧l=2)∨(k=2∧l=2)) (x : integralLattice C) :
    integralRepresentation D (integralOperator C neg i k (integralOperator C neg j l x))=0 :=
  integral_mixed_operator_zero D neg neg i j k l
    (rational_mixed_ad_zero A hd hs hp ho neg i j hij k l hkl) x

theorem all_ring_original_mixed_zero (K : Type*) [CommRing K] (neg : Bool) (i j : Fin r)
    (hij : integerPairing A (s₀ i:Roots A).val (s₀ j:Roots A).val=0)
    (k l : ℕ) (hkl : (k=2∧l=1)∨(k=1∧l=2)∨(k=2∧l=2))
    (x : K⊗[ℤ]integralLattice C) :
    baseChange D K ((integralOperator C neg i k).baseChange K
      ((integralOperator C neg j l).baseChange K x))=0 :=
  baseChange_mixed_operator_zero D K neg neg i j k l
    (rational_mixed_ad_zero A hd hs hp ho neg i j hij k l hkl) x

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalMixedOperators
