import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Replicate

/-! Positive weighted label multisets expand to ordinary label multisets.
Grouping the weights at each label retains the entire weighted multiset,
including repeated blocks. This is the elementary counting interface for
actual prime-power decomposition labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.WeightedMultisetPartitionExpansion
variable {α : Type*}

def expand (B : Multiset (α × ℕ)) : Multiset α :=
  B.bind (fun b => Multiset.replicate b.2 b.1)

def partsAt (B : Multiset (α × ℕ)) (a : α) : Multiset ℕ :=
  (B.filter (fun b => b.1 = a)).map Prod.snd

theorem count_expand (B : Multiset (α × ℕ)) (a : α) :
    (expand B).count a = (partsAt B a).sum := by
  induction B using Multiset.induction with
  | empty => simp [expand, partsAt]
  | cons b B ih =>
    simp only [expand, partsAt] at ih
    rcases b with ⟨b, n⟩
    by_cases h : b = a
    · subst b
      simp [expand, partsAt, ih]
    · simp [expand, partsAt, Multiset.count_replicate, h, ih]

theorem count_partsAt (B : Multiset (α × ℕ)) (a : α) (n : ℕ) :
    (partsAt B a).count n = B.count (a, n) := by
  induction B using Multiset.induction with
  | empty => simp [partsAt]
  | cons b B ih =>
    simp only [partsAt] at ih
    rcases b with ⟨b, m⟩
    by_cases h : b = a
    · subst b
      simp [partsAt, Multiset.count_cons, ih]
    · simp [partsAt, Multiset.count_cons, h, Ne.symm h, ih]

theorem partsAt_positive (B : Multiset (α × ℕ))
    (hB : ∀ b ∈ B, 0 < b.2) (a : α) :
    ∀ n ∈ partsAt B a, 0 < n := by
  intro n hn
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hn
  exact hB b (Multiset.mem_filter.mp hb).1

theorem partsAt_injective {B C : Multiset (α × ℕ)}
    (h : ∀ a, partsAt B a = partsAt C a) : B = C := by
  apply Multiset.ext.mpr
  rintro ⟨a, n⟩
  have hc := congrArg (fun s : Multiset ℕ => s.count n) (h a)
  simpa only [count_partsAt] using hc

end SymmetricSubgroupAsymptotics.WeightedMultisetPartitionExpansion
