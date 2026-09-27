import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-! Exact natural-number geometry of marker collapse, including both
parities, zero defect, and the number of profiles at each fixed defect.
The balance equation retains the original and collapsed support sizes.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.MarkerGeometry

structure Parameters (N epsilon : ℕ) where
  M : ℕ
  g : ℕ
  f : ℕ
  q : ℕ
  parity : epsilon ≤ 1
  balance : 2 * N + epsilon + 2 * q = 2 * M + 3 * g + f
  q_le_g : q ≤ g
  q_le_M : q ≤ M
  positive_signs : g = 0 ∨ 1 ≤ q

namespace Parameters

variable {N epsilon : ℕ}

def defect (s : Parameters N epsilon) : ℕ := (s.g + s.f - epsilon) / 2
def repeats (s : Parameters N epsilon) : ℕ := s.g - s.q

theorem defect_balance (s : Parameters N epsilon) :
    s.g + s.f = 2 * s.defect + epsilon := by
  have hb := s.balance
  have he := s.parity
  have hq := s.q_le_g
  unfold defect
  omega

theorem degree_balance (s : Parameters N epsilon) :
    N = s.M + s.defect + s.repeats := by
  have hb := s.balance
  have hd := s.defect_balance
  have hq := s.q_le_g
  unfold repeats
  omega

theorem defect_le (s : Parameters N epsilon) : s.defect ≤ N := by
  have h := s.degree_balance
  omega

theorem repeats_le_two_defect (s : Parameters N epsilon) :
    s.repeats ≤ 2 * s.defect := by
  have hd := s.defect_balance
  have hp := s.positive_signs
  have he := s.parity
  unfold repeats
  omega

theorem repeats_le_remaining (s : Parameters N epsilon) :
    s.repeats ≤ N - s.defect := by
  have h := s.degree_balance
  omega

theorem markers_le (s : Parameters N epsilon) : s.g ≤ 2 * s.defect + 1 := by
  have h := s.defect_balance
  have he := s.parity
  omega

theorem selected_le_three_defect (s : Parameters N epsilon) (hD : 1 ≤ s.defect) :
    s.q ≤ 3 * s.defect := by
  have h := s.markers_le
  have hq := s.q_le_g
  omega

/-- The only zero-defect states are the empty marker family, possibly
with the one odd fixed point, and the one natural S3 marker. -/
theorem zero_defect (s : Parameters N epsilon) (hD : s.defect = 0) :
    (s.g = 0 ∧ s.f = epsilon ∧ s.q = 0) ∨
      (epsilon = 1 ∧ s.g = 1 ∧ s.f = 0 ∧ s.q = 1) := by
  have h := s.defect_balance
  have he := s.parity
  have hq := s.q_le_g
  have hp := s.positive_signs
  omega

theorem ext {s t : Parameters N epsilon}
    (hM : s.M = t.M) (hg : s.g = t.g) (hf : s.f = t.f) (hq : s.q = t.q) : s = t := by
  cases s
  cases t
  cases hM
  cases hg
  cases hf
  cases hq
  rfl

end Parameters

def DefectFibre (N epsilon D : ℕ) :=
  {s : Parameters N epsilon // s.defect = D}

def profileCode {N epsilon D : ℕ} (s : DefectFibre N epsilon D) :
    Fin (2 * D + 2) × Fin (2 * D + 2) := by
  have hg := s.1.markers_le
  have hq := s.1.q_le_g
  have hd := s.2
  exact (⟨s.1.g, by omega⟩, ⟨s.1.q, by omega⟩)

theorem profileCode_injective {N epsilon D : ℕ} :
    Function.Injective (@profileCode N epsilon D) := by
  intro s t h
  have hg : s.1.g = t.1.g := congrArg (fun z => z.1.val) h
  have hq : s.1.q = t.1.q := congrArg (fun z => z.2.val) h
  have hs := s.1.defect_balance
  have ht := t.1.defect_balance
  have hsd := s.2
  have htd := t.2
  have hsb := s.1.balance
  have htb := t.1.balance
  apply Subtype.ext
  apply Parameters.ext <;> omega

/-- A concrete injection gives the entire profile count at fixed defect;
no profile-cardinality bound is assumed. -/
theorem card_defect_fibre_le (N epsilon D : ℕ) :
    Nat.card (DefectFibre N epsilon D) ≤ (2 * D + 2) ^ 2 := by
  have h := Nat.card_le_card_of_injective (@profileCode N epsilon D) profileCode_injective
  simpa only [Nat.card_prod, Nat.card_fin, pow_two] using h

end SymmetricSubgroupAsymptotics.MarkerGeometry
