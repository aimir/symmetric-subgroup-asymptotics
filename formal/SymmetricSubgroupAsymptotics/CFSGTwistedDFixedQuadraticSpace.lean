import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleCharts

/-! The actual defining-fixed vectors form a vector space over the
literal Frobenius-fixed field. The original split quadratic form takes
values in that field and restricts to a bundled quadratic form, retaining
Q itself in characteristic two. No Witt-index assertion is built in. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticSpace
open CFSGOrthogonalDSerreMatrices CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists
open CFSGTwistedDFixedVectorCardinality CFSGOrthogonalDIndexBundledQuadratic

def fixedSpace (n : ℕ) (q : CFSG.PrimePower) :
    Submodule (fixedField q) (Index (n + 2) → q.Extension 2) where
  carrier := {v | vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) v = v}
  zero_mem' := by
    funext x
    change definingFieldAutomorphism q 2 0 = 0
    exact map_zero _
  add_mem' := by
    intro v w hv hw
    funext x
    change definingFieldAutomorphism q 2 (_ + _) = v x + w x
    rw [map_add]
    exact congrArg₂ (fun a b : q.Extension 2 => a + b) (congrFun hv x) (congrFun hw x)
  smul_mem' := by
    intro a v hv
    funext x
    change definingFieldAutomorphism q 2
      ((a : q.Extension 2) * v (CFSGOrthogonalDGenerationForkTorus.flip n x)) =
        (a : q.Extension 2) * v x
    have ha : definingFieldAutomorphism q 2 (a : q.Extension 2) = (a : q.Extension 2) := a.property
    rw [map_mul, ha]
    exact congrArg (fun b : q.Extension 2 => (a : q.Extension 2) * b) (congrFun hv x)

def fixedCarrierEquiv (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace n q ≃ fixedVectors n q := Equiv.refl _

theorem fixedSpace_card (n : ℕ) (q : CFSG.PrimePower) :
    Nat.card (fixedSpace n q) = q.order ^ (2 * (n + 2)) :=
  (Nat.card_congr (fixedCarrierEquiv n q)).trans
    (CFSGTwistedDFixedVectorParametrization.fixedVectors_card n q)

def quadraticValue (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace n q) : fixedField q :=
  ⟨splitQuadraticForm (q.Extension 2) (n + 2) v.val,
    CFSGTwistedDFixedPoleCharts.norm_fixed n q (fixedCarrierEquiv n q v)⟩

theorem polar_value (n : ℕ) (q : CFSG.PrimePower) (v w : fixedSpace n q) :
    ((QuadraticMap.polar (quadraticValue n q) v w : fixedField q) : q.Extension 2) =
      QuadraticMap.polar (splitQuadraticForm (q.Extension 2) (n + 2)) v.val w.val := rfl

def fixedQuadraticForm (n : ℕ) (q : CFSG.PrimePower) :
    QuadraticForm (fixedField q) (fixedSpace n q) :=
  QuadraticMap.ofPolar (quadraticValue n q)
    (by
      intro a v
      apply Subtype.ext
      change splitQuadraticForm (q.Extension 2) (n + 2) ((a : q.Extension 2) • v.val) =
        ((a : q.Extension 2) * (a : q.Extension 2)) •
          splitQuadraticForm (q.Extension 2) (n + 2) v.val
      exact (splitQuadraticForm (q.Extension 2) (n + 2)).map_smul _ _)
    (by
      intro v w z
      apply Subtype.ext
      change QuadraticMap.polar (splitQuadraticForm (q.Extension 2) (n + 2))
          (v.val + w.val) z.val = _
      exact QuadraticMap.polar_add_left (splitQuadraticForm (q.Extension 2) (n + 2)) _ _ _)
    (by
      intro a v w
      apply Subtype.ext
      change QuadraticMap.polar (splitQuadraticForm (q.Extension 2) (n + 2))
          ((a : q.Extension 2) • v.val) w.val = _
      exact QuadraticMap.polar_smul_left (splitQuadraticForm (q.Extension 2) (n + 2)) _ _ _)

theorem fixedQuadraticForm_apply (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace n q) :
    ((fixedQuadraticForm n q v : fixedField q) : q.Extension 2) =
      splitQuadraticForm (q.Extension 2) (n + 2) v.val := rfl

theorem fixedQuadraticForm_polar (n : ℕ) (q : CFSG.PrimePower) (v w : fixedSpace n q) :
    (((fixedQuadraticForm n q).polarBilin v w : fixedField q) : q.Extension 2) =
      (splitQuadraticForm (q.Extension 2) (n + 2)).polarBilin v.val w.val := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticSpace
