import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ZMod
import Lean.Elab.Tactic.Omega

/-!
# Independent selections from distinct nonzero binary labels

At most 2^k-1 nonzero labels lie in the span of k independent labels.
The remaining labels extend the original selection. Counting these actual
extensions gives a uniform lower bound, in particular (q-7)^4 ordered
independent four-selections among q distinct nonzero binary characters.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.IndependentBinarySelections

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (s : Finset V)

abbrev Frame (n : ℕ) := {v : Fin n → s // LinearIndependent (ZMod 2) (fun i => (v i : V))}

def frameSpan {n : ℕ} (v : Frame s n) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range (fun i => (v.val i : V)))

theorem frameSpan_card {n : ℕ} (v : Frame s n) : Nat.card (frameSpan s v) = 2 ^ n := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  congr 1
  simpa only [frameSpan, Fintype.card_fin] using finrank_span_eq_card v.property

abbrev Extension {n : ℕ} (v : Frame s n) := {x : s // (x : V) ∉ frameSpan s v}

/-- The zero vector is excluded from the original label set, hence only
2^n-1 labels can be forbidden by the retained actual span. -/
theorem extension_card_lower (hzero : (0 : V) ∉ s) {n : ℕ} (v : Frame s n) :
    s.card + 1 - 2 ^ n ≤ Nat.card (Extension s v) := by
  let W := frameSpan s v
  let f : {x : s // (x : V) ∈ W} → {w : W // w ≠ 0} :=
    fun x => ⟨⟨x.val.val, x.property⟩, by
      intro hx
      apply hzero
      have he : x.val.val = 0 := congrArg Subtype.val hx
      exact he ▸ x.val.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.val) h))
  have hcard := Nat.card_le_card_of_injective f hf
  have hW : Nat.card {w : W // w ≠ 0} = 2 ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [Fintype.card_subtype_eq]
    rw [← Nat.card_eq_fintype_card, frameSpan_card]
  rw [hW] at hcard
  have he : Nat.card (Extension s v) = s.card - Nat.card {x : s // (x : V) ∈ W} := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {x : s // ¬ (x : V) ∈ W} = _
    rw [Fintype.card_subtype_compl, Fintype.card_coe, ← Nat.card_eq_fintype_card]
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  omega

def extend {n : ℕ} (z : Σ v : Frame s n, Extension s v) : Frame s (n + 1) :=
  ⟨Fin.cons z.2.val z.1.val, by
    change LinearIndependent (ZMod 2) (Subtype.val ∘ Fin.cons z.2.val z.1.val)
    rw [Fin.comp_cons]
    exact z.1.property.finCons z.2.property⟩

theorem extend_injective {n : ℕ} : Function.Injective (extend s (n := n)) := by
  rintro ⟨v,x⟩ ⟨w,y⟩ h
  have he : (Fin.cons x.val v.val : Fin (n + 1) → s) =
      Fin.cons y.val w.val := congrArg Subtype.val h
  obtain ⟨hx,hv⟩ := Fin.cons_injective2 he
  have hv' : v = w := Subtype.ext hv
  subst w
  have hx' : x = y := Subtype.ext hx
  subst y
  rfl

/-- Uniform greedy counting, retaining the actual independent selections.
The auxiliary r bounds the dimension of every preceding span. -/
theorem frame_card_lower (hzero : (0 : V) ∉ s) (r k : ℕ) (hk : k ≤ r + 1) :
    (s.card + 1 - 2 ^ r) ^ k ≤ Nat.card (Frame s k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    haveI : Nonempty (Frame s 0) :=
      ⟨⟨Fin.elim0, linearIndependent_empty_type⟩⟩
    exact Nat.card_pos
  | succ k ih =>
    have hik := ih (by omega)
    have hstep : (s.card + 1 - 2 ^ r) * Nat.card (Frame s k) ≤
        Nat.card (Σ v : Frame s k, Extension s v) := by
      rw [Nat.card_sigma]
      calc
        _ = ∑ _v : Frame s k, (s.card + 1 - 2 ^ r) := by
          simp [Nat.card_eq_fintype_card, mul_comm]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro v _
          have hp : 2 ^ k ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
          exact (Nat.sub_le_sub_left hp _).trans (extension_card_lower s hzero v)
    calc
      (s.card + 1 - 2 ^ r) ^ (k + 1) =
          (s.card + 1 - 2 ^ r) * (s.card + 1 - 2 ^ r) ^ k := by rw [pow_succ, mul_comm]
      _ ≤ (s.card + 1 - 2 ^ r) * Nat.card (Frame s k) := Nat.mul_le_mul_left _ hik
      _ ≤ Nat.card (Σ v : Frame s k, Extension s v) := hstep
      _ ≤ Nat.card (Frame s (k + 1)) :=
        Nat.card_le_card_of_injective (extend s) (extend_injective s)

theorem four_frame_card_lower (hzero : (0 : V) ∉ s) :
    (s.card - 7) ^ 4 ≤ Nat.card (Frame s 4) := by
  have h := frame_card_lower s hzero 3 4 (by decide)
  have he : s.card + 1 - 2 ^ 3 = s.card - 7 := by omega
  rwa [he] at h

end SymmetricSubgroupAsymptotics.IndependentBinarySelections
