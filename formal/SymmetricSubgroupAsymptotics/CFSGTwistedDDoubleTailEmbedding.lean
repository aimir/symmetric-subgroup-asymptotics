import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedTailLinear
import SymmetricSubgroupAsymptotics.CFSGTwistedDHighestPairOperator

/-! Literal fixed-field embedding and restriction after the first two
hyperbolic pairs. The retained tail is the SAME defining-fixed quadratic
space; both first positive axes are perpendicular to its image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDoubleTailEmbedding
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedTailLinear
open CFSGTwistedDHighestPairOperator CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPrefixPerpendicular

def tailEmbed (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace n q →ₗ[fixedField q] fixedSpace (n + 1) q where
  toFun z := (poleEquiv n q).symm (0, (z, 0))
  map_add' z w := by
    rw [← map_add]
    simp only [Prod.mk_add_mk, zero_add]
  map_smul' a z := by
    rw [← map_smul]
    simp only [Prod.smul_def, smul_zero, RingHom.id_apply]

theorem pole_tailEmbed (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace n q) :
    poleEquiv n q (tailEmbed n q z) = (0, (z, 0)) :=
  (poleEquiv n q).apply_symm_apply _

theorem tailEmbed_positiveHead (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace n q) :
    positiveHead n q (tailEmbed n q z) = 0 :=
  congrArg Prod.fst (pole_tailEmbed n q z)

theorem tailEmbed_negativeHead (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace n q) :
    negativeHead n q (tailEmbed n q z) = 0 :=
  congrArg (fun x => x.2.2) (pole_tailEmbed n q z)

theorem tailEmbed_tail (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace n q) :
    tailLinear n q (tailEmbed n q z) = z :=
  congrArg (fun x => x.2.1) (pole_tailEmbed n q z)

theorem tailEmbed_quadratic (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace n q) :
    fixedQuadraticForm (n + 1) q (tailEmbed n q z) = fixedQuadraticForm n q z := by
  rw [quadratic_coordinates, tailEmbed_positiveHead, tailEmbed_negativeHead,
    tailEmbed_tail, zero_mul, zero_add]

def doubleEmbed (s : ℕ) (q : CFSG.PrimePower) :
    fixedSpace s q →ₗ[fixedField q] fixedSpace (s + 2) q :=
  (tailEmbed (s + 1) q).comp (tailEmbed s q)

def doubleRestriction (s : ℕ) (q : CFSG.PrimePower) :
    fixedSpace (s + 2) q →ₗ[fixedField q] fixedSpace s q :=
  (tailLinear s q).comp (tailLinear (s + 1) q)

theorem doubleRestriction_doubleEmbed (s : ℕ) (q : CFSG.PrimePower) (z : fixedSpace s q) :
    doubleRestriction s q (doubleEmbed s q z) = z := by
  change tailLinear s q (tailLinear (s + 1) q
    (tailEmbed (s + 1) q (tailEmbed s q z))) = z
  rw [tailEmbed_tail, tailEmbed_tail]

theorem doubleEmbed_quadratic (s : ℕ) (q : CFSG.PrimePower) (z : fixedSpace s q) :
    fixedQuadraticForm (s + 2) q (doubleEmbed s q z) = fixedQuadraticForm s q z := by
  change fixedQuadraticForm (s + 2) q (tailEmbed (s + 1) q (tailEmbed s q z)) = _
  rw [tailEmbed_quadratic, tailEmbed_quadratic]

theorem first_polar (s : ℕ) (q : CFSG.PrimePower) (v : fixedSpace (s + 2) q) :
    (fixedQuadraticForm (s + 2) q).polarBilin (firstVector s q) v =
      negativeHead (s + 1) q v := by
  apply Subtype.ext
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar, firstVector_val]
  change CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2)
    (Pi.single (Sum.inl 0) 1) v.val = v.val (Sum.inr 0)
  rw [polar_positive_basis]

theorem second_polar (s : ℕ) (q : CFSG.PrimePower) (v : fixedSpace (s + 2) q) :
    (fixedQuadraticForm (s + 2) q).polarBilin (secondVector s q) v =
      negativeHead s q (tailLinear (s + 1) q v) := by
  apply Subtype.ext
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar, secondVector_val]
  change CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2)
    (Pi.single (Sum.inl (CFSGOrthogonalDIndexFlagVectors.secondIndex s)) 1) v.val = v.val (Sum.inr 1)
  rw [polar_positive_basis]
  rfl

theorem doubleEmbed_perp_first (s : ℕ) (q : CFSG.PrimePower) (z : fixedSpace s q) :
    (fixedQuadraticForm (s + 2) q).polarBilin (firstVector s q) (doubleEmbed s q z) = 0 := by
  rw [first_polar]
  exact tailEmbed_negativeHead (s + 1) q (tailEmbed s q z)

theorem doubleEmbed_perp_second (s : ℕ) (q : CFSG.PrimePower) (z : fixedSpace s q) :
    (fixedQuadraticForm (s + 2) q).polarBilin (secondVector s q) (doubleEmbed s q z) = 0 := by
  rw [second_polar]
  change negativeHead s q (tailLinear (s + 1) q
    (tailEmbed (s + 1) q (tailEmbed s q z))) = 0
  rw [tailEmbed_tail, tailEmbed_negativeHead]

end SymmetricSubgroupAsymptotics.CFSGTwistedDDoubleTailEmbedding
