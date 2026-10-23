import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGTrialityFixedWeylWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTripleRootPolynomial
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylConjugationTransport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalTripleCubicRelations

/-! Integral cubic coefficients for the ORIGINAL G2 folded generators
in the SAME D4 Geck matrices. The third coefficient is literal and is
never divided after reduction. The singleton uses third coefficient zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckIntegralCoefficients
open CFSGGTwoD4GeckGenerators CFSGGTwoD4GeckSerreRepresentation
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGTrialityFixedWeylWords
open CFSGNormTwoGeckTripleRootPolynomial CFSGNormTwoGeckOrthogonalProducts
open CFSGSerreQuadraticMatrix CFSGNormTwoRootPairing CFSGIntegerMatrixPairing
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
abbrev IntMat := Matrix CFSGGTwoD4GeckGenerators.GeckIndex CFSGGTwoD4GeckGenerators.GeckIndex ℤ

theorem outer_orthogonal (i j : Fin 3) (hij : i≠j) :
    integerPairing A (Index (outerNode i):Roots A).val (Index (outerNode j):Roots A).val=0 := by
  change (A).toBilin' (Pi.single (outerNode i) (1:ℤ) : Fin 4→ℤ)
    (Pi.single (outerNode j) (1:ℤ) : Fin 4→ℤ)=0
  rw [Matrix.toBilin'_single]
  exact outerNode_cartan i j hij

private theorem outer_root_commute_rational (neg : Bool) (i j : Fin 3) :
    Commute (fieldRoot rawData ℚ neg (outerNode i)) (fieldRoot rawData ℚ neg (outerNode j)) := by
  by_cases hij : i=j
  · subst j
    exact Commute.refl _
  · have hc : CFSGGeckSerreRepresentation.cartan Base Index (outerNode i) (outerNode j)=0 := by
      rw [cartan_eq]
      exact outerNode_cartan i j hij
    cases neg
    · have he := CFSGGeckSerreRepresentation.serreE Base Index (outerNode i) (outerNode j)
      rw [hc] at he
      simp only [neg_zero,Int.toNat_zero,pow_zero,Module.End.one_apply] at he
      have hroot (k : Fin 4) : fieldRoot rawData ℚ false k=CFSGGeckSerreRepresentation.E Base Index k :=
        CFSGGeckIntegralMatrices.map_E Base (Index k)
      change _*_=_*_
      rw [hroot,hroot]
      exact sub_eq_zero.mp he
    · have he := CFSGGeckSerreRepresentation.serreF Base Index (outerNode i) (outerNode j)
      rw [hc] at he
      simp only [neg_zero,Int.toNat_zero,pow_zero,Module.End.one_apply] at he
      have hroot (k : Fin 4) : fieldRoot rawData ℚ true k=CFSGGeckSerreRepresentation.F Base Index k :=
        CFSGGeckIntegralMatrices.map_F Base (Index k)
      change _*_=_*_
      rw [hroot,hroot]
      exact sub_eq_zero.mp he

theorem outer_root_commute (neg : Bool) (i j : Fin 3) :
    Commute (fieldRoot rawData ℤ neg (outerNode i)) (fieldRoot rawData ℤ neg (outerNode j)) := by
  change _*_=_*_
  apply CFSGSerreSquareZeroMatrix.integerCast_injective CFSGGTwoD4GeckGenerators.GeckIndex
  change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix (_*_)
  simp only [map_mul,map_fieldRoot]
  exact (outer_root_commute_rational neg i j).eq

theorem outer_root_second_zero (neg : Bool) (i j : Fin 3) :
    fieldRoot rawData ℤ neg (outerNode i)*fieldSecond rawData ℤ neg (outerNode j)=0 := by
  by_cases hij : i=j
  · subst j
    exact fieldRoot_mul_second rawData ℤ neg (outerNode i)
  · exact first_mul_orthogonal_second_zero A hs hp Base
      (signedSimpleRoot A hs hp Base Index neg (outerNode j))
      (signedSimpleRoot A hs hp Base Index neg (outerNode i))
      (signed_orthogonal A hs hp Base Index neg _ _ (outer_orthogonal j i (Ne.symm hij))) _ _
      (root_signed_degree A hs hp Base Index ℤ neg (outerNode i))
      (second_signed_degree A hs hp Base Index ℤ neg (outerNode j))

theorem outer_second_root_zero (neg : Bool) (i j : Fin 3) :
    fieldSecond rawData ℤ neg (outerNode i)*fieldRoot rawData ℤ neg (outerNode j)=0 := by
  by_cases hij : i=j
  · subst j
    exact fieldSecond_mul_root rawData ℤ neg (outerNode i)
  · exact second_mul_orthogonal_first_zero A hs hp Base
      (signedSimpleRoot A hs hp Base Index neg (outerNode i))
      (signedSimpleRoot A hs hp Base Index neg (outerNode j))
      (signed_orthogonal A hs hp Base Index neg _ _ (outer_orthogonal i j hij)) _ _
      (second_signed_degree A hs hp Base Index ℤ neg (outerNode i))
      (root_signed_degree A hs hp Base Index ℤ neg (outerNode j))

def integerRoot (neg : Bool) (i : Fin 2) : IntMat :=
  if i=0 then tripleFirst A hs hp Base Index ℤ neg outerNode else fieldRoot rawData ℤ neg 1

def integerSecond (neg : Bool) (i : Fin 2) : IntMat :=
  if i=0 then tripleSecond A hs hp Base Index ℤ neg outerNode else fieldSecond rawData ℤ neg 1

def integerThird (neg : Bool) (i : Fin 2) : IntMat :=
  if i=0 then tripleThird A hs hp Base Index ℤ neg outerNode else 0

theorem integer_cubic (neg : Bool) (i : Fin 2) :
    integerRoot neg i*integerRoot neg i=integerSecond neg i+integerSecond neg i ∧
      integerRoot neg i*integerSecond neg i=integerThird neg i+integerThird neg i+integerThird neg i ∧
      integerSecond neg i*integerRoot neg i=integerThird neg i+integerThird neg i+integerThird neg i ∧
      integerRoot neg i*integerThird neg i=0 ∧ integerThird neg i*integerRoot neg i=0 := by
  fin_cases i
  · exact CFSGOrthogonalTripleCubicRelations.triple_relations
      (fun j=>fieldRoot rawData ℤ neg (outerNode j))
      (fun j=>fieldSecond rawData ℤ neg (outerNode j))
      (outer_root_commute neg) (fun j=>fieldRoot_square rawData ℤ neg (outerNode j))
      (outer_root_second_zero neg) (outer_second_root_zero neg)
  · exact ⟨fieldRoot_square rawData ℤ neg 1,
      by simpa only [integerRoot,integerSecond,integerThird,show (1:Fin 2)≠0 by decide,
        if_false,zero_add] using fieldRoot_mul_second rawData ℤ neg 1,
      by simpa only [integerRoot,integerSecond,integerThird,show (1:Fin 2)≠0 by decide,
        if_false,zero_add] using fieldSecond_mul_root rawData ℤ neg 1,
      by simp [integerThird,Fin.ext_iff],
      by simp [integerThird,Fin.ext_iff]⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckIntegralCoefficients
