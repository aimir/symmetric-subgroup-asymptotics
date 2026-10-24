import SymmetricSubgroupAsymptotics.BinaryQuadraticLevelCardinality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases

/-! The actual binary quadratic isometry group in characteristic two.
With nonzero leading and cross coefficients, its first-column orbit
has at most 2q elements and its first-column stabilizer at most two.
Thus its order is at most 4q. All matrices and preserved values are
literal; no orthogonal-group recognition or order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.BinaryQuadraticIsometryLeadingCardinality

open BinaryQuadraticLevelCardinality
variable {K : Type*} [Field K]

abbrev GeneralLinear := (Matrix (Fin 2) (Fin 2) K)ˣ

def vectorEval (a b c : K) (v : Fin 2 → K) : K := eval a b c (v 0, v 1)

def isometries (a b c : K) : Subgroup (GeneralLinear (K := K)) where
  carrier := {g | ∀ v : Fin 2 → K, vectorEval a b c (g.val *ᵥ v) = vectorEval a b c v}
  one_mem' := by intro v; rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' := by
    intro g h hg hh v
    change vectorEval a b c ((g.val * h.val) *ᵥ v) = _
    rw [← Matrix.mulVec_mulVec, hg, hh]
  inv_mem' := by
    intro g hg v
    have he := hg ((g⁻¹).val *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec] at he
    exact he.symm

theorem polar [CharP K 2] (a b c : K) (v w : Fin 2 → K) :
    vectorEval a b c (v + w) - vectorEval a b c v - vectorEval a b c w =
      b * (v 0 * w 1 + w 0 * v 1) := by
  dsimp [vectorEval, eval, Pi.add_apply]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem det_eq_one [CharP K 2] (a b c : K) (hb : b ≠ 0) (g : isometries a b c) :
    g.val.val.det = 1 := by
  let e0 : Fin 2 → K := Pi.single 0 1
  let e1 : Fin 2 → K := Pi.single 1 1
  have he : b * (g.val.val 0 0 * g.val.val 1 1 + g.val.val 0 1 * g.val.val 1 0) = b := by
    calc
      _ = vectorEval a b c (g.val.val *ᵥ e0 + g.val.val *ᵥ e1) -
          vectorEval a b c (g.val.val *ᵥ e0) - vectorEval a b c (g.val.val *ᵥ e1) := by
        rw [polar]
        simp only [e0, e1, Matrix.mulVec_single_one, Matrix.col_apply]
      _ = vectorEval a b c (e0 + e1) - vectorEval a b c e0 - vectorEval a b c e1 := by
        rw [← Matrix.mulVec_add, g.property, g.property, g.property]
      _ = b := by
        simp [e0, e1, vectorEval, eval]
        ring
  have hd : g.val.val 0 0 * g.val.val 1 1 + g.val.val 0 1 * g.val.val 1 0 = 1 :=
    mul_left_cancel₀ hb (he.trans (mul_one b).symm)
  simpa only [Matrix.det_fin_two, sub_eq_add_neg, CharTwo.neg_eq] using hd

private theorem fixed_first_entries [CharP K 2] (a b c : K) (hb : b ≠ 0)
    (g : isometries a b c)
    (hg : g.val.val *ᵥ Pi.single (0 : Fin 2) 1 = Pi.single (0 : Fin 2) 1) :
    g.val.val 0 0 = 1 ∧ g.val.val 1 0 = 0 ∧ g.val.val 1 1 = 1 := by
  have h0 : g.val.val 0 0 = 1 := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_same] using congrFun hg 0
  have h1 : g.val.val 1 0 = 0 := by
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using congrFun hg 1
  have hdet := det_eq_one a b c hb g
  rw [Matrix.det_fin_two, h0, h1, one_mul, mul_zero, sub_zero] at hdet
  exact ⟨h0, h1, hdet⟩

private abbrev matrixAction (a b c : K) : MulAction (isometries a b c) (Fin 2 → K) where
  smul g v := g.val.val *ᵥ v
  one_smul v := Matrix.one_mulVec v
  mul_smul g h v := (Matrix.mulVec_mulVec v g.val.val h.val.val).symm

theorem card_le_four_mul_card_of_leading_ne_zero [Finite K] [CharP K 2]
    (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card (isometries a b c) ≤ 4 * Nat.card K := by
  letI : MulAction (isometries a b c) (Fin 2 → K) := matrixAction a b c
  let e0 : Fin 2 → K := Pi.single 0 1
  let O := MulAction.orbit (isometries a b c) e0
  let S := MulAction.stabilizer (isometries a b c) e0
  let encodeOrbit : O → {v : K × K // eval a b c v = a} := fun y =>
    ⟨(y.val 0, y.val 1), by
      obtain ⟨g, hg⟩ := y.property
      change g.val.val *ᵥ e0 = y.val at hg
      change vectorEval a b c y.val = a
      rw [← hg, g.property]
      simp [vectorEval, eval, e0]⟩
  have hOrbitInjective : Function.Injective encodeOrbit := by
    intro y z he
    have hv : (y.val 0, y.val 1) = (z.val 0, z.val 1) :=
      congrArg (fun v : {v : K × K // eval a b c v = a} => v.val) he
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg Prod.fst hv
    · exact congrArg Prod.snd hv
  have hO : Nat.card O ≤ 2 * Nat.card K :=
    (Nat.card_le_card_of_injective encodeOrbit hOrbitInjective).trans
      (level_card_le_two_mul_card a b c a hb ha)
  let encodeStabilizer : S → {t : K // a * t ^ 2 + b * t + c = c} := fun g =>
    ⟨g.val.val.val 0 1, by
      have hh : g.val.val.val *ᵥ e0 = e0 := by
        exact g.property
      obtain ⟨_, _, h11⟩ := fixed_first_entries a b c hb g.val hh
      have he := g.val.property (Pi.single (1 : Fin 2) 1)
      simpa only [vectorEval, eval, Matrix.mulVec_single_one, Matrix.col_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        h11, one_pow, mul_one, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
        add_zero, zero_add] using he⟩
  have hStabilizerInjective : Function.Injective encodeStabilizer := by
    intro g h he
    have h01 : g.val.val.val 0 1 = h.val.val.val 0 1 :=
      congrArg (fun t : {t : K // a * t ^ 2 + b * t + c = c} => t.val) he
    have hg : g.val.val.val *ᵥ e0 = e0 := g.property
    have hh : h.val.val.val *ᵥ e0 = e0 := h.property
    obtain ⟨g00, g10, g11⟩ := fixed_first_entries a b c hb g.val hg
    obtain ⟨h00, h10, h11⟩ := fixed_first_entries a b c hb h.val hh
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · change g.val.val.val 0 0 = h.val.val.val 0 0
      exact g00.trans h00.symm
    · change g.val.val.val 0 1 = h.val.val.val 0 1
      exact h01
    · change g.val.val.val 1 0 = h.val.val.val 1 0
      exact g10.trans h10.symm
    · change g.val.val.val 1 1 = h.val.val.val 1 1
      exact g11.trans h11.symm
  have hS : Nat.card S ≤ 2 :=
    (Nat.card_le_card_of_injective encodeStabilizer hStabilizerInjective).trans
      (quadratic_fibre_card_le_two a b c c ha)
  calc
    Nat.card (isometries a b c) = Nat.card O * Nat.card S := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (isometries a b c) e0)).symm
    _ ≤ (2 * Nat.card K) * 2 := Nat.mul_le_mul hO hS
    _ = 4 * Nat.card K := by ring

end SymmetricSubgroupAsymptotics.BinaryQuadraticIsometryLeadingCardinality
