import SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveDirectionProducts
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation

/-! Commutation with the literal positive simple matrices propagates
to all positive chain and alternating paired directions, through the
proved coefficient-one sparse products. No unipotent presentation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveDirectionClosure
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGOrthogonalDIndexPositiveCentralizer CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDPositiveDirectionProducts
variable (K : Type) [Field K]

theorem chain_directions (r : ℕ) (A : Mat K r)
    (hA : ∀ i : Fin r, A * positive K r i = positive K r i * A) :
    ∀ i j : Fin r, i < j → A * chainMatrix K r i j = chainMatrix K r i j * A := by
  have hadj (i j : Fin r) (hij : i.val + 1 = j.val) :
      A * chainMatrix K r i j = chainMatrix K r i j * A := by
    have hi : i.val + 1 < r := by rw [hij]; exact j.isLt
    have he : (⟨i.val + 1, hi⟩ : Fin r) = j := Fin.ext hij
    have h := hA i
    rw [positive, dif_pos hi, he] at h
    exact h
  have haux (d : ℕ) : ∀ i j : Fin r, i < j → j.val - i.val = d →
      A * chainMatrix K r i j = chainMatrix K r i j * A := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i j hij hd
      by_cases ha : i.val + 1 = j.val
      · exact hadj i j ha
      let k : Fin r := ⟨j.val - 1, by have := j.isLt; omega⟩
      have hik : i < k := by
        change i.val < j.val - 1
        change i.val < j.val at hij
        omega
      have hkj : k < j := by
        change j.val - 1 < j.val
        have := i.isLt
        change i.val < j.val at hij
        omega
      have hk : k.val + 1 = j.val := by
        change j.val - 1 + 1 = j.val
        change i.val < j.val at hij
        omega
      have hs : k.val - i.val < d := by
        change j.val - 1 - i.val < d
        change i.val < j.val at hij
        omega
      have hleft := ih (k.val - i.val) hs i k hik rfl
      have hright := hadj k j hk
      have h := commutes_bracket A (chainMatrix K r i k) (chainMatrix K r k j) hleft hright
      simpa only [chain_chain K r i k j (ne_of_lt hik) (ne_of_lt hkj) (ne_of_lt hij)] using h
  intro i j hij
  exact haux (j.val - i.val) i j hij rfl

theorem pair_directions (n : ℕ) (A : Mat K (n + 2))
    (hA : ∀ i : Fin (n + 2), A * positive K (n + 2) i = positive K (n + 2) i * A) :
    ∀ i j : Fin (n + 2), i ≠ j → A * pairedUpper K i j = pairedUpper K i j * A := by
  have hc := chain_directions K (n + 2) A hA
  have hfork : A * pairedUpper K (pen n) (last n) = pairedUpper K (pen n) (last n) * A := by
    have h := hA (last n)
    rw [CFSGOrthogonalDTerminalRootCommutation.positive_last] at h
    exact h
  have hlast (i : Fin (n + 2)) (hi : i < last n) :
      A * pairedUpper K i (last n) = pairedUpper K i (last n) * A := by
    by_cases hip : i = pen n
    · simpa only [hip] using hfork
    have hpen : i < pen n := by
      change i.val < n
      have hh : i.val ≠ n := fun h => hip (Fin.ext h)
      change i.val < n + 1 at hi
      omega
    have h := commutes_bracket A (chainMatrix K (n + 2) i (pen n))
      (pairedUpper K (pen n) (last n)) (hc i (pen n) hpen) hfork
    simpa only [chain_pair_first K (n + 2) i (pen n) (last n)
      (ne_of_lt hpen) (pen_ne_last n) (ne_of_lt hi)] using h
  have hlt (i j : Fin (n + 2)) (hij : i < j) :
      A * pairedUpper K i j = pairedUpper K i j * A := by
    by_cases hj : j = last n
    · subst j
      exact hlast i hij
    have hjl : j < last n := by
      change j.val < n + 1
      have hb := j.isLt
      have hn : j.val ≠ n + 1 := fun h => hj (Fin.ext h)
      omega
    have hil : i < last n := hij.trans hjl
    have h := commutes_bracket A (chainMatrix K (n + 2) j (last n))
      (pairedUpper K i (last n)) (hc j (last n) hjl) (hlast i hil)
    simpa only [chain_pair_second K (n + 2) i j (last n)
      (ne_of_lt hij) (ne_of_lt hjl) (ne_of_lt hil)] using h
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · have he : pairedUpper K i j = -pairedUpper K j i := by
      unfold pairedUpper
      abel
    rw [he, mul_neg, neg_mul]
    exact congrArg (fun M : Mat K (n + 2) => -M) (hlt j i h)

end SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveDirectionClosure
