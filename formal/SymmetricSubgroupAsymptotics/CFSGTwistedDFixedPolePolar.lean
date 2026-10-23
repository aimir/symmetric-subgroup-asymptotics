import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedTailLinear
import Mathlib.Tactic.Ring

/-! Exact polar and quadratic coordinates of the actual fixed-space
first hyperbolic pair and its smaller fixed tail. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPolePolar
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedTailLinear CFSGTwistedA2FixedField

theorem positiveHead_inv (n : ℕ) (q : CFSG.PrimePower)
    (a b : fixedField q) (z : fixedSpace n q) :
    positiveHead n q ((poleEquiv n q).symm (a, (z, b))) = a :=
  congrArg Prod.fst ((poleEquiv n q).apply_symm_apply (a, (z, b)))

theorem negativeHead_inv (n : ℕ) (q : CFSG.PrimePower)
    (a b : fixedField q) (z : fixedSpace n q) :
    negativeHead n q ((poleEquiv n q).symm (a, (z, b))) = b :=
  congrArg (fun x => x.2.2) ((poleEquiv n q).apply_symm_apply (a, (z, b)))

theorem tailLinear_inv (n : ℕ) (q : CFSG.PrimePower)
    (a b : fixedField q) (z : fixedSpace n q) :
    tailLinear n q ((poleEquiv n q).symm (a, (z, b))) = z :=
  congrArg (fun x => x.2.1) ((poleEquiv n q).apply_symm_apply (a, (z, b)))

theorem quadratic_inv (n : ℕ) (q : CFSG.PrimePower)
    (a b : fixedField q) (z : fixedSpace n q) :
    fixedQuadraticForm (n + 1) q ((poleEquiv n q).symm (a, (z, b))) =
      a * b + fixedQuadraticForm n q z := by
  rw [quadratic_coordinates, positiveHead_inv, negativeHead_inv, tailLinear_inv]

theorem polar_coordinates (n : ℕ) (q : CFSG.PrimePower)
    (v w : fixedSpace (n + 1) q) :
    (fixedQuadraticForm (n + 1) q).polarBilin v w =
      positiveHead n q v * negativeHead n q w + positiveHead n q w * negativeHead n q v +
        (fixedQuadraticForm n q).polarBilin (tailLinear n q v) (tailLinear n q w) := by
  change fixedQuadraticForm (n + 1) q (v + w) - fixedQuadraticForm (n + 1) q v -
    fixedQuadraticForm (n + 1) q w = _
  rw [quadratic_coordinates, quadratic_coordinates, quadratic_coordinates]
  simp only [map_add]
  change (positiveHead n q v + positiveHead n q w) *
      (negativeHead n q v + negativeHead n q w) +
      fixedQuadraticForm n q (tailLinear n q v + tailLinear n q w) -
      (positiveHead n q v * negativeHead n q v + fixedQuadraticForm n q (tailLinear n q v)) -
      (positiveHead n q w * negativeHead n q w + fixedQuadraticForm n q (tailLinear n q w)) =
    positiveHead n q v * negativeHead n q w + positiveHead n q w * negativeHead n q v +
      (fixedQuadraticForm n q (tailLinear n q v + tailLinear n q w) -
        fixedQuadraticForm n q (tailLinear n q v) - fixedQuadraticForm n q (tailLinear n q w))
  ring

theorem polar_inv (n : ℕ) (q : CFSG.PrimePower)
    (a b c d : fixedField q) (z z' : fixedSpace n q) :
    (fixedQuadraticForm (n + 1) q).polarBilin
      ((poleEquiv n q).symm (a, (z, b))) ((poleEquiv n q).symm (c, (z', d))) =
      a * d + c * b + (fixedQuadraticForm n q).polarBilin z z' := by
  rw [polar_coordinates, positiveHead_inv, positiveHead_inv,
    negativeHead_inv, negativeHead_inv, tailLinear_inv, tailLinear_inv]

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPolePolar
