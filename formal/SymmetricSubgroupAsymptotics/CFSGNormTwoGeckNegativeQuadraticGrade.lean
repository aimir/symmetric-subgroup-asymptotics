import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPrimitiveRootEntry
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixSupportTransport
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Both actual coefficients of every negative simple root polynomial
retain their literal integral lattice degrees in every characteristic.
The first coefficient has an original unit entry, including at bad primes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeQuadraticGrade
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckNegativeLatticeDegree CFSGNormTwoGeckPrimitiveRootEntry
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWordLatticeSupport
open CFSGGradedMatrixSupport CFSGGradedQuadraticUnit
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s
local notation "ell" => latticeWeight A hs hp b

theorem field_F_support (K : Type) [CommRing K] (i : Fin r) :
    Supported ell (fun v=>v-(s i:Roots A).val) (fieldRoot D K true i) := by
  change Supported ell (fun v=>v-(s i:Roots A).val)
    ((Int.castRingHom K).mapMatrix (CFSGGeckIntegralMatrices.F b (s i)))
  apply CFSGIntegerMatrixSupportTransport.map_support
  rw [CFSGGeckIntegralMatrices.map_F]
  exact rational_F_lattice_support A hs hp b (s i)

theorem field_F_unit_entry (K : Type) [CommRing K] (i : Fin r) :
    fieldRoot D K true i (Sum.inl (s i)) (Sum.inr (s i:Roots A))=1 := by
  change (CFSGGeckIntegralMatrices.F b (s i) (Sum.inl (s i)) (Sum.inr (s i:Roots A)):K)=1
  rw [integer_F_unit_entry A hs hp b (s i),Int.cast_one]

theorem rational_negative_second_support (i : Fin r) :
    Supported ell (fun v=>v+(-(s i:Roots A).val+ -(s i:Roots A).val))
      (fieldSecond D ℚ true i) := by
  have hF := field_F_support A hs hp b s ℚ i
  have hprod : Supported ell (fun v=>v+(-(s i:Roots A).val+ -(s i:Roots A).val))
      (fieldRoot D ℚ true i*fieldRoot D ℚ true i) := by
    apply supported_congr (supported_mul hF hF)
    intro v
    dsimp only [Function.comp_apply]
    abel
  intro j k hjk
  have hz := hprod j k hjk
  have hh := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ=>M j k)
    (fieldRoot_square D ℚ true i)
  change (fieldRoot D ℚ true i*fieldRoot D ℚ true i) j k=
    fieldSecond D ℚ true i j k+fieldSecond D ℚ true i j k at hh
  rw [hz] at hh
  linarith

theorem field_negative_second_support (K : Type) [CommRing K] (i : Fin r) :
    Supported ell (fun v=>v+(-(s i:Roots A).val+ -(s i:Roots A).val))
      (fieldSecond D K true i) := by
  exact CFSGIntegerMatrixSupportTransport.map_support ell _ ((D).integerSecond true i)
    (rational_negative_second_support A hs hp b s i) K

theorem negative_quadraticGrade (K : Type) [Field K] (i : Fin r) (a : K) :
    QuadraticGrade ell (-(s i:Roots A).val) (canonicalRoot D K true i a) := by
  refine ⟨a • fieldRoot D K true i,a^2 • fieldSecond D K true i,
    canonicalRoot_val D K true i a,?_,?_⟩
  · apply supported_smul
    simpa only [sub_eq_add_neg] using field_F_support A hs hp b s K i
  · exact supported_smul ell _ _ (field_negative_second_support A hs hp b s K i) (a^2)

theorem word_negative_quadraticGrade (K : Type) [Field K]
    (w : List (Fin r)) (i : Fin r) (a : K) :
    QuadraticGrade ell (wordLinear A hs hp b s w (-(s i:Roots A).val))
      (wordUnit A hs hp b s K w*canonicalRoot D K true i a*(wordUnit A hs hp b s K w)⁻¹) := by
  have hP := word_lattice_support A hs hp b s K w
  have hQ := word_lattice_support A hs hp b s K (inverseWord w)
  rw [wordUnit_inverseWord,wordLinear_inverseWord] at hQ
  exact conjugate ell (-(s i:Roots A).val) (wordLinear A hs hp b s w).toAddEquiv
    (wordUnit A hs hp b s K w) (canonicalRoot D K true i a) hP hQ
    (negative_quadraticGrade A hs hp b s K i a)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeQuadraticGrade
