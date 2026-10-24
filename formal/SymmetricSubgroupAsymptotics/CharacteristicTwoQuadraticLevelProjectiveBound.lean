import SymmetricSubgroupAsymptotics.BinaryQuadraticLevelCardinality
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.CharP.Two

/-! In characteristic two, a nonzero homogeneous quadratic level meets
each projective ray in at most one vector. This gives q+1 for every
binary quadratic level, without a conic classification or census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.CharacteristicTwoQuadraticLevelProjectiveBound

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem level_nonzero (Q : V → K) (h0 : Q 0 = 0)
    (t : K) (ht : t ≠ 0) (v : {v : V // Q v = t}) : v.val ≠ 0 := by
  intro hv
  apply ht
  calc
    t = Q v.val := v.property.symm
    _ = Q 0 := congrArg Q hv
    _ = 0 := h0

/-- The actual projective ray containing a vector on the nonzero level. -/
def levelToProjectivization (Q : V → K) (h0 : Q 0 = 0) (t : K) (ht : t ≠ 0) :
    {v : V // Q v = t} → ℙ K V :=
  fun v => Projectivization.mk K v.val (level_nonzero Q h0 t ht v)

/-- Square injectivity in characteristic two makes the ray map injective. -/
theorem levelToProjectivization_injective [CharP K 2]
    (Q : V → K) (h0 : Q 0 = 0)
    (hscale : ∀ (a : K) (v : V), Q (a • v) = a ^ 2 * Q v)
    (t : K) (ht : t ≠ 0) :
    Function.Injective (levelToProjectivization Q h0 t ht) := by
  intro v w he
  have hv := level_nonzero Q h0 t ht v
  have hw := level_nonzero Q h0 t ht w
  change Projectivization.mk K v.val hv = Projectivization.mk K w.val hw at he
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff K v.val w.val hv hw).mp he
  change (u : K) • w.val = v.val at hu
  have hs : (u : K) ^ 2 * t = t := by
    calc
      (u : K) ^ 2 * t = (u : K) ^ 2 * Q w.val :=
        congrArg (fun x : K => (u : K) ^ 2 * x) w.property.symm
      _ = Q ((u : K) • w.val) := (hscale u w.val).symm
      _ = Q v.val := congrArg Q hu
      _ = t := v.property
  have hs1 : (u : K) ^ 2 = 1 := mul_right_cancel₀ ht (hs.trans (one_mul t).symm)
  have hu1 : (u : K) = 1 := CharTwo.sq_injective (hs1.trans (one_pow 2).symm)
  apply Subtype.ext
  rw [← hu, hu1, one_smul]

theorem level_card_le_projective_card [Finite K] [Finite V] [CharP K 2]
    (Q : V → K) (h0 : Q 0 = 0)
    (hscale : ∀ (a : K) (v : V), Q (a • v) = a ^ 2 * Q v)
    (t : K) (ht : t ≠ 0) :
    Nat.card {v : V // Q v = t} ≤ Nat.card (ℙ K V) :=
  Nat.card_le_card_of_injective (levelToProjectivization Q h0 t ht)
    (levelToProjectivization_injective Q h0 hscale t ht)

/-- Every nonzero binary quadratic level has at most q+1 vectors.
The cross coefficient may vanish; only the level is required nonzero. -/
theorem binary_level_card_le_card_add_one [Finite K] [CharP K 2]
    (a b c t : K) (ht : t ≠ 0) :
    Nat.card {v : K × K // BinaryQuadraticLevelCardinality.eval a b c v = t} ≤
      Nat.card K + 1 := by
  have h0 : BinaryQuadraticLevelCardinality.eval a b c (0 : K × K) = 0 := by
    simp [BinaryQuadraticLevelCardinality.eval]
  have hscale (s : K) (v : K × K) :
      BinaryQuadraticLevelCardinality.eval a b c (s • v) =
        s ^ 2 * BinaryQuadraticLevelCardinality.eval a b c v := by
    change a * (s * v.1) ^ 2 + b * (s * v.1) * (s * v.2) + c * (s * v.2) ^ 2 =
      s ^ 2 * (a * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2)
    ring
  have h := level_card_le_projective_card
    (BinaryQuadraticLevelCardinality.eval a b c) h0 hscale t ht
  have hp : Nat.card (ℙ K (K × K)) = Nat.card K + 1 := by
    simpa [Finset.sum_range_succ, add_comm] using
      (Projectivization.card_of_finrank K (K × K) (n := 2) (by simp))
  exact h.trans_eq hp

end SymmetricSubgroupAsymptotics.CharacteristicTwoQuadraticLevelProjectiveBound
