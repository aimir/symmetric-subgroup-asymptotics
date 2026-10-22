import SymmetricSubgroupAsymptotics.CFSGQuadraticParameterizedCollecting
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRationalRootValues
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRootAdditive
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCollectingPairCubes

/-! The actual rational adjacent collecting word at TWO arbitrary
parameters. There are no new root-space or nilpotence hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalParameterizedCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckParameterizedWeyl
open CFSGNormTwoGeckRationalWeylCollecting CFSGNormTwoGeckCollectingPairCubes
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem adjacent_word (i j : Fin r) (hij : cartan b s i j= -1) (t a : ℚ) :
    canonicalRoot (realizationData A hs hp b s) ℚ false i t*
      canonicalRoot (realizationData A hs hp b s) ℚ false j a*
      (canonicalRoot (realizationData A hs hp b s) ℚ false i t)⁻¹*
      (canonicalRoot (realizationData A hs hp b s) ℚ false j a)⁻¹=
      canonicalWeyl (realizationData A hs hp b s) ℚ i*
        canonicalRoot (realizationData A hs hp b s) ℚ false j (a*t)*
        (canonicalWeyl (realizationData A hs hp b s) ℚ i)⁻¹ := by
  let D := realizationData A hs hp b s
  let x := fieldRoot D ℚ false j
  let y := ⁅fieldRoot D ℚ false i,x⁆
  have hweyl : (canonicalWeyl D ℚ i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)*x*
      (((canonicalWeyl D ℚ i)⁻¹ : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)ˣ) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)=y := by
    simpa only [parameterWeyl,canonicalWeyl,Units.val_one,inv_one] using
      weyl_conjugate_adjacent A hs hp b s i j hij
  have hword := CFSGQuadraticParameterizedCollecting.conjugate_scaled_difference
    (canonicalRoot D ℚ false i t) (canonicalWeyl D ℚ i) x y
    (collecting_pair_commute A hs hp b s i j hij)
    (fieldRoot_cube D ℚ false j) t a
    (conjugate_adjacent A hs hp b s i j hij t) hweyl
  have ha : (canonicalRoot D ℚ false j a : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)=
      1+a • x+(a^2/2) • x^2 := canonicalRoot_val_rational D false j a
  have hna : (((canonicalRoot D ℚ false j a)⁻¹ : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)ˣ) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)=
      1+(-a) • x+((-a)^2/2) • x^2 := by
    rw [canonicalRoot_inverse]
    exact canonicalRoot_val_rational D false j (-a)
  have hat : (canonicalRoot D ℚ false j (a*t) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)=
      1+(a*t) • x+((a*t)^2/2) • x^2 := canonicalRoot_val_rational D false j (a*t)
  apply Units.ext
  change (canonicalRoot D ℚ false i t : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)*
    (canonicalRoot D ℚ false j a : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)*
      (((canonicalRoot D ℚ false i t)⁻¹ : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)ˣ) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)*
      (((canonicalRoot D ℚ false j a)⁻¹ : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)ˣ) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)=
    (canonicalWeyl D ℚ i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)*
      (canonicalRoot D ℚ false j (a*t) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)*
      (((canonicalWeyl D ℚ i)⁻¹ : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)ˣ) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)
  rw [ha,hna,hat]
  exact hword

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalParameterizedCollecting
