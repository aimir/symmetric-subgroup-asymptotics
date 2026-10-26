import SymmetricSubgroupAsymptotics.RestrictedPartitionCardinalityRecurrence
import Mathlib.Data.List.GetD

/-! Local finite certificates for restricted partition counts. Validity
checks only a bounded grid of integer recurrence equations; it does not
enumerate partitions. The row program is a memoized producer for the
selected size-sixteen pilot. Larger certificates can be supplied as
literal rows without re-running a recursive count for every entry. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.RestrictedPartitionFiniteTableCertificate
open RestrictedPartitionCardinalityRecurrence

def Valid (N : ℕ) (t : ℕ → ℕ → ℕ) : Prop :=
  (∀ k : Fin (N+1),t 0 k.val=1) ∧
  (∀ n : Fin N,t (n.val+1) 0=0) ∧
  ∀ n k : Fin (N+1),k.val<N →
    t n.val (k.val+1)=t n.val k.val+
      (if k.val+1≤n.val then t (n.val-(k.val+1)) (k.val+1) else 0)

theorem count_eq_entry (N : ℕ) (t : ℕ → ℕ → ℕ) (h : Valid N t)
    (n k : ℕ) (hn : n≤N) (hk : k≤N) : count n k=t n k := by
  have hmain : ∀ s n k : ℕ,n+k=s → n≤N → k≤N → count n k=t n k := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro n k he hn hk
      cases n with
      | zero =>
        have hz := h.1 ⟨k,by omega⟩
        simpa only [count] using hz.symm
      | succ n =>
        cases k with
        | zero =>
          have hz := h.2.1 ⟨n,by omega⟩
          simpa only [count] using hz.symm
        | succ k =>
          have hni : n+1<N+1 := by omega
          have hki : k<N+1 := by omega
          have hkn : k<N := by omega
          have hs := h.2.2 (⟨n+1,hni⟩ : Fin (N+1)) (⟨k,hki⟩ : Fin (N+1)) hkn
          change t (n+1) (k+1)=t (n+1) k+
            (if k+1≤n+1 then t ((n+1)-(k+1)) (k+1) else 0) at hs
          rw [count,hs]
          rw [ih ((n+1)+k) (by omega) (n+1) k rfl hn (by omega)]
          split_ifs with hle
          · rw [ih (((n+1)-(k+1))+(k+1)) (by omega)
              ((n+1)-(k+1)) (k+1) rfl (by omega) hk]
          · rfl
  exact hmain (n+k) n k rfl hn hk

theorem partition_card_eq_entry (N : ℕ) (t : ℕ → ℕ → ℕ) (h : Valid N t)
    (n : ℕ) (hn : n≤N) : Nat.card (Nat.Partition n)=t n n :=
  (partition_card_eq_count n).trans (count_eq_entry N t h n n hn hn)

def nextRow (k : ℕ) (previous : List ℕ) : List ℕ :=
  (List.range previous.length).foldl
    (fun row n => row++[previous.getD n 0+
      (if k≤n then row.getD (n-k) 0 else 0)]) []

def memoRows (N : ℕ) : List (List ℕ) :=
  (List.range N).foldl
    (fun rows k => rows++[nextRow (k+1) (rows.getLastD [])])
    [1::List.replicate N 0]

def memoEntry (N n k : ℕ) : ℕ := ((memoRows N).getD k []).getD n 0

theorem memo_sixteen_valid : Valid 16 (memoEntry 16) := by
  unfold Valid
  decide +kernel

theorem memo_sixteen_partition_card : Nat.card (Nat.Partition 16)=231 := by
  have h := partition_card_eq_entry 16 (memoEntry 16) memo_sixteen_valid 16 (by decide)
  exact h.trans (by decide +kernel)

end SymmetricSubgroupAsymptotics.RestrictedPartitionFiniteTableCertificate
