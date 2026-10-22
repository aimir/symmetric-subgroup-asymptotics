import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPrimitiveRootEntry
import SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveConjugatePair

/-! Two original Weyl-word negative-root coefficients of the same literal
integral degree differ only by an integral sign. Generated-Lie line
recognition proves rational proportionality; original primitive entries
and integer inverse words prove that its scalar is a unit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordComparison
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWordLatticeSupport
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckPrimitiveRootEntry CFSGSerreQuadraticWeylWord
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀

def coefficient (w : List (Fin r)) (i : Fin r) : Mat :=
  CFSGAlgebraConjugationAction.action ℚ Mat (wordUnit A hs hp b₀ s₀ ℚ w)
    (RootPairing.GeckConstruction.f (s₀ i))

omit [(rootPairing A hs hp).IsReduced] in
theorem coefficient_mem (w : List (Fin r)) (i : Fin r) :
    coefficient A hd hs hp ho w i∈RootPairing.GeckConstruction.lieAlgebra b₀ :=
  CFSGNormTwoGeckGeneratedLieInvariance.word_action_mem_generated A hs hp b₀ s₀ w _
    (RootPairing.GeckConstruction.f_mem_lieAlgebra (s₀ i))

omit [(rootPairing A hs hp).IsReduced] in
theorem coefficient_degree (w : List (Fin r)) (i : Fin r) :
    Supported ell (fun x=>x+wordLinear A hs hp b₀ s₀ w (-(s₀ i:Roots A).val))
      (coefficient A hd hs hp ho w i) := by
  have hP := word_lattice_support A hs hp b₀ s₀ ℚ w
  have hQ := word_lattice_support A hs hp b₀ s₀ ℚ (inverseWord w)
  rw [wordUnit_inverseWord,wordLinear_inverseWord] at hQ
  have hF := CFSGNormTwoGeckNegativeLatticeDegree.rational_F_lattice_support A hs hp b₀ (s₀ i)
  have hh := supported_conjugation ell (wordLinear A hs hp b₀ s₀ w).toAddEquiv
    (-(s₀ i:Roots A).val) _ _ _ hP (by simpa only [sub_eq_add_neg] using hF) hQ
  exact hh

theorem same_degree_sign (w v : List (Fin r)) (i j : Fin r)
    (hdegree : wordLinear A hs hp b₀ s₀ w (-(s₀ i:Roots A).val)=
      wordLinear A hs hp b₀ s₀ v (-(s₀ j:Roots A).val)) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧
      coefficient A hd hs hp ho w i=(ε:ℚ) • coefficient A hd hs hp ho v j := by
  have hdeg := coefficient_degree A hd hs hp ho w i
  rw [hdegree] at hdeg
  obtain ⟨c,hc⟩ := CFSGNormTwoCoordinateGeneratedRootLine.word_degree_line A hd hs hp ho
    v j (coefficient A hd hs hp ho w i) (coefficient_mem A hd hs hp ho w i) hdeg
  have hcast : (Int.castRingHom ℚ).mapMatrix
      ((canonicalWord D ℤ w : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℤ)*
        CFSGGeckIntegralMatrices.F b₀ (s₀ i)*
          (((canonicalWord D ℤ w)⁻¹ : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℤ)ˣ) :
            Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℤ))=
      c • (Int.castRingHom ℚ).mapMatrix
      ((canonicalWord D ℤ v : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℤ)*
        CFSGGeckIntegralMatrices.F b₀ (s₀ j)*
          (((canonicalWord D ℤ v)⁻¹ : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℤ)ˣ) :
            Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℤ)) := by
    simp only [map_mul,cast_integer_word,cast_integer_word_inverse,CFSGGeckIntegralMatrices.map_F]
    exact hc
  have hsign := CFSGIntegralPrimitiveConjugatePair.scalar_eq_sign
    (canonicalWord D ℤ w) (canonicalWord D ℤ v)
    (CFSGGeckIntegralMatrices.F b₀ (s₀ i)) (CFSGGeckIntegralMatrices.F b₀ (s₀ j))
    (Sum.inl (s₀ i)) (Sum.inr (s₀ i:Roots A))
    (Sum.inl (s₀ j)) (Sum.inr (s₀ j:Roots A))
    (integer_F_unit_entry A hs hp b₀ (s₀ i)) (integer_F_unit_entry A hs hp b₀ (s₀ j)) c hcast
  rcases hsign with hsign | hsign
  · refine ⟨1,Or.inl rfl,?_⟩
    simpa only [hsign,Int.cast_one] using hc
  · refine ⟨-1,Or.inr rfl,?_⟩
    simpa only [hsign,Int.cast_neg,Int.cast_one] using hc

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordComparison
