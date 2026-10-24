import Mathlib.Data.List.OfFn
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi

/-! A finite, dimension-uniform cover for multisets of binary interior
coefficient words. A word of length d records a monic polynomial of degree
d+1 with constant coefficient one. Enumeration is over coefficient words,
never over matrices or group elements. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryWeightedMultisetCodes

def words (n : ℕ) : Finset (List Bool) :=
  Finset.univ.image (List.ofFn : (Fin n → Bool) → List Bool)

theorem mem_words_iff (l : List Bool) (n : ℕ) : l ∈ words n ↔ l.length = n := by
  constructor
  · rintro hl
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hl
    exact List.length_ofFn
  · intro hl
    subst n
    exact Finset.mem_image.mpr ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩

def weight (m : Multiset (List Bool)) : ℕ :=
  (m.map (fun l => l.length + 1)).sum

def codes : ℕ → Finset (Multiset (List Bool))
  | 0 => {0}
  | n + 1 => (Finset.range (n + 1)).biUnion (fun d =>
      (words d).biUnion (fun l => (codes (n - d)).image (fun m => l ::ₘ m)))
termination_by n => n
decreasing_by omega

theorem mem_codes_weight (m : Multiset (List Bool)) : m ∈ codes (weight m) := by
  induction m using Multiset.induction_on with
  | empty => simp [weight, codes]
  | @cons l m ih =>
    have hw : weight (l ::ₘ m) = (l.length + weight m) + 1 := by
      simp only [weight, Multiset.map_cons, Multiset.sum_cons]
      omega
    rw [hw, codes]
    apply Finset.mem_biUnion.mpr
    refine ⟨l.length, Finset.mem_range.mpr (by omega), ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨l, (mem_words_iff l l.length).mpr rfl, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨m, by simpa only [Nat.add_sub_cancel_left] using ih, rfl⟩

theorem card_codes_four : (codes 4).card = 18 := by decide +kernel

theorem card_codes_six : (codes 6).card = 104 := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryWeightedMultisetCodes
