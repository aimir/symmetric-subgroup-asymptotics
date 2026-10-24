import SymmetricSubgroupAsymptotics.BinarySymmetricSquareAction
import SymmetricSubgroupAsymptotics.BinaryQuadraticIsometryCardinality
import SymmetricSubgroupAsymptotics.FieldFunctionalMultiplicationDuality

/-! A base-field functional stabilizer injects into an actual binary
quadratic isometry group. All extension-field multiples of rank-one
matrices are tested, rather than a single value of the functional. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.BinaryQuadraticFunctionalStabilizer

open BinarySymmetricSquareAction
open FieldFunctionalMultiplicationDuality
variable {K : Type*} [Field K]

def rankOne (v : Fin 2 → K) : Space (K := K) :=
  ⟨Matrix.vecMulVec v v, Matrix.transpose_vecMulVec v v⟩

theorem rankOne_congruence (A : GeneralLinear (K := K)) (v : Fin 2 → K) :
    congruenceLinearMap A (rankOne v) = rankOne (A.val *ᵥ v) := by
  apply Subtype.ext
  change A.val * Matrix.vecMulVec v v * A.val.transpose =
    Matrix.vecMulVec (A.val *ᵥ v) (A.val *ᵥ v)
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- Literal coefficients on the three symmetric entries. -/
def coefficientLinearMap (a b c : K) : Space (K := K) →ₗ[K] K where
  toFun S := a * S.val 0 0 + b * S.val 0 1 + c * S.val 1 1
  map_add' S T := by
    change a * (S.val 0 0 + T.val 0 0) + b * (S.val 0 1 + T.val 0 1) +
      c * (S.val 1 1 + T.val 1 1) = _
    ring
  map_smul' t S := by
    change a * (t * S.val 0 0) + b * (t * S.val 0 1) + c * (t * S.val 1 1) =
      t * (a * S.val 0 0 + b * S.val 0 1 + c * S.val 1 1)
    ring

variable {F : Type*} [Field F] [Algebra F K]

/-- This functional is linear over F; no K-linearity of f is asserted. -/
def functional (f : Module.Dual F K) (a b c : K) : Module.Dual F (Space (K := K)) :=
  f.comp ((coefficientLinearMap a b c).restrictScalars F)

theorem functional_scaled_rankOne (f : Module.Dual F K) (a b c t : K)
    (v : Fin 2 → K) :
    functional f a b c (t • rankOne v) =
      f (t * BinaryQuadraticIsometryLeadingCardinality.vectorEval a b c v) := by
  change f (a * (t * (v 0 * v 0)) + b * (t * (v 0 * v 1)) +
    c * (t * (v 1 * v 1))) = _
  congr 1
  dsimp [BinaryQuadraticIsometryLeadingCardinality.vectorEval,
    BinaryQuadraticLevelCardinality.eval]
  ring

/-- The subgroup preserving the entire actual functional on symmetric matrices. -/
def preservers (f : Module.Dual F K) (a b c : K) :
    Subgroup (GeneralLinear (K := K)) where
  carrier := {A | ∀ S : Space (K := K),
    functional f a b c (congruenceLinearMap A S) = functional f a b c S}
  one_mem' := by intro S; rw [congruenceLinearMap_one]
  mul_mem' := by
    intro A B hA hB S
    rw [congruenceLinearMap_mul, hA, hB]
  inv_mem' := by
    intro A hA S
    have he := hA (congruenceLinearMap A⁻¹ S)
    rw [← congruenceLinearMap_mul, mul_inv_cancel, congruenceLinearMap_one] at he
    exact he.symm

/-- Testing all scaled rank-one matrices recovers actual K-valued
quadratic preservation from F-valued functional preservation. -/
theorem preserver_isometry (f : Module.Dual F K) (hf : f ≠ 0) (a b c : K)
    (A : preservers f a b c) :
    A.val ∈ BinaryQuadraticIsometryLeadingCardinality.isometries a b c := by
  intro v
  apply multiplicationFunctional_injective f hf
  apply LinearMap.ext
  intro t
  have he := A.property (t • rankOne v)
  rw [(congruenceLinearMap A.val).map_smul, rankOne_congruence,
    functional_scaled_rankOne, functional_scaled_rankOne] at he
  change f (BinaryQuadraticIsometryLeadingCardinality.vectorEval a b c (A.val.val *ᵥ v) * t) =
    f (BinaryQuadraticIsometryLeadingCardinality.vectorEval a b c v * t)
  simpa only [mul_comm] using he

/-- The actual functional-preserver group has order at most 4q. -/
theorem card_preservers_le_four_mul_card [Finite K] [CharP K 2]
    (f : Module.Dual F K) (hf : f ≠ 0) (a b c : K) (hb : b ≠ 0) :
    Nat.card (preservers f a b c) ≤ 4 * Nat.card K := by
  let j : preservers f a b c →
      BinaryQuadraticIsometryLeadingCardinality.isometries a b c :=
    fun A => ⟨A.val, preserver_isometry f hf a b c A⟩
  have hj : Function.Injective j := by
    intro A B he
    apply Subtype.ext
    exact congrArg
      (fun g : BinaryQuadraticIsometryLeadingCardinality.isometries a b c => g.val) he
  exact (Nat.card_le_card_of_injective j hj).trans
    (BinaryQuadraticIsometryCardinality.card_le_four_mul_card a b c hb)

end SymmetricSubgroupAsymptotics.BinaryQuadraticFunctionalStabilizer
