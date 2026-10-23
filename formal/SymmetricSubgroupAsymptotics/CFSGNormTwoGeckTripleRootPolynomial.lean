import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalProducts
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeQuadraticGrade
import SymmetricSubgroupAsymptotics.CFSGQuadraticTripleProduct

/-! The product of three actual orthogonal simple-root units is a
literal integral cubic polynomial, for both signs and every coefficient
ring. Its third coefficient is retained as E0*E1*E2; no division by three
or false quadratic truncation is used. This is a matrix-unit identity,
not a faithfulness assertion for an original or twisted source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTripleRootPolynomial
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckNegativeQuadraticGrade CFSGGradedMatrixSupport
open CFSGNormTwoGeckOrthogonalProducts CFSGSerreQuadraticMatrix
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s
local notation "ell" => latticeWeight A hs hp b

def signedSimpleRoot (neg : Bool) (i : Fin r) : Roots A :=
  if neg then negativeIndex A hs hp (s i) else s i

theorem root_signed_degree (K : Type) [CommRing K] (neg : Bool) (i : Fin r) :
    Supported ell (fun v=>v+(signedSimpleRoot A hs hp b s neg i).val) (fieldRoot D K neg i) := by
  cases neg
  · exact field_E_lattice_support A hs hp b s K i
  · simpa only [signedSimpleRoot,if_true,negative_val,sub_eq_add_neg] using
      field_F_support A hs hp b s K i

theorem second_signed_degree (K : Type) [CommRing K] (neg : Bool) (i : Fin r) :
    Supported ell (fun v=>v+(2:ℤ) • (signedSimpleRoot A hs hp b s neg i).val)
      (fieldSecond D K neg i) := by
  cases neg
  · exact field_second_lattice_support A hs hp b s K i
  · simpa only [signedSimpleRoot,if_true,negative_val,two_smul] using
      field_negative_second_support A hs hp b s K i

theorem signed_orthogonal (neg : Bool) (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val=0) :
    integerPairing A (signedSimpleRoot A hs hp b s neg i).val
      (signedSimpleRoot A hs hp b s neg j).val=0 := by
  cases neg
  · exact hij
  · simpa only [signedSimpleRoot,if_true,negative_val,map_neg,LinearMap.neg_apply,neg_neg] using hij

def tripleFirst (K : Type) [CommRing K] (neg : Bool) (u : Fin 3→Fin r) :
    Matrix (b.support⊕Roots A) (b.support⊕Roots A) K :=
  fieldRoot D K neg (u 0)+fieldRoot D K neg (u 1)+fieldRoot D K neg (u 2)

def tripleSecond (K : Type) [CommRing K] (neg : Bool) (u : Fin 3→Fin r) :
    Matrix (b.support⊕Roots A) (b.support⊕Roots A) K :=
  fieldSecond D K neg (u 0)+fieldSecond D K neg (u 1)+fieldSecond D K neg (u 2)+
    fieldRoot D K neg (u 0)*fieldRoot D K neg (u 1)+
    fieldRoot D K neg (u 0)*fieldRoot D K neg (u 2)+
    fieldRoot D K neg (u 1)*fieldRoot D K neg (u 2)

def tripleThird (K : Type) [CommRing K] (neg : Bool) (u : Fin 3→Fin r) :
    Matrix (b.support⊕Roots A) (b.support⊕Roots A) K :=
  fieldRoot D K neg (u 0)*fieldRoot D K neg (u 1)*fieldRoot D K neg (u 2)

theorem canonicalRootTriple_val (K : Type) [CommRing K] (neg : Bool) (u : Fin 3→Fin r)
    (horth : ∀i j : Fin 3,i≠j→integerPairing A (s (u i):Roots A).val (s (u j):Roots A).val=0)
    (t : K) :
    (↑(canonicalRoot D K neg (u 0) t*canonicalRoot D K neg (u 1) t*
      canonicalRoot D K neg (u 2) t) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)=
      1+t • tripleFirst A hs hp b s K neg u+t^2 • tripleSecond A hs hp b s K neg u+
        t^3 • tripleThird A hs hp b s K neg u := by
  let E : Fin 3→Matrix (b.support⊕Roots A) (b.support⊕Roots A) K :=
    fun j=>fieldRoot D K neg (u j)
  let Q : Fin 3→Matrix (b.support⊕Roots A) (b.support⊕Roots A) K :=
    fun j=>fieldSecond D K neg (u j)
  let a : Fin 3→Roots A := fun j=>signedSimpleRoot A hs hp b s neg (u j)
  have ha (i j : Fin 3) (hij : i≠j) : integerPairing A (a i).val (a j).val=0 :=
    signed_orthogonal A hs hp b s neg (u i) (u j) (horth i j hij)
  have hEQ (i j : Fin 3) (hij : i≠j) : E i*Q j=0 :=
    first_mul_orthogonal_second_zero A hs hp b (a j) (a i) (ha j i (Ne.symm hij))
      (E i) (Q j) (root_signed_degree A hs hp b s K neg (u i))
      (second_signed_degree A hs hp b s K neg (u j))
  have hQE (i j : Fin 3) (hij : i≠j) : Q i*E j=0 :=
    second_mul_orthogonal_first_zero A hs hp b (a i) (a j) (ha i j hij)
      (Q i) (E j) (second_signed_degree A hs hp b s K neg (u i))
      (root_signed_degree A hs hp b s K neg (u j))
  have hQQ (i j : Fin 3) (hij : i≠j) : Q i*Q j=0 :=
    second_mul_orthogonal_second_zero A hs hp b (a i) (a j) (ha i j hij)
      (Q i) (Q j) (second_signed_degree A hs hp b s K neg (u i))
      (second_signed_degree A hs hp b s K neg (u j))
  simp only [Units.val_mul,canonicalRoot_val]
  change CFSGQuadraticTripleProduct.value (E 0) (Q 0) t*
    CFSGQuadraticTripleProduct.value (E 1) (Q 1) t*
    CFSGQuadraticTripleProduct.value (E 2) (Q 2) t=
      1+t • (E 0+E 1+E 2)+t^2 • (Q 0+Q 1+Q 2+E 0*E 1+E 0*E 2+E 1*E 2)+
        t^3 • (E 0*E 1*E 2)
  exact CFSGQuadraticTripleProduct.product_three (E 0) (E 1) (E 2) (Q 0) (Q 1) (Q 2) t
    (hEQ 0 1 (by decide)) (hQE 0 1 (by decide)) (hQQ 0 1 (by decide))
    (hEQ 0 2 (by decide)) (hEQ 1 2 (by decide)) (hQE 0 2 (by decide))
    (hQE 1 2 (by decide)) (hQQ 0 2 (by decide)) (hQQ 1 2 (by decide))

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTripleRootPolynomial
