import SymmetricSubgroupAsymptotics.RectangleSymmetricChains
import Mathlib.Data.Fintype.Card

/-! Ranked symmetric-chain partitions and their exact middle-layer width
consequence. The rectangle constructor is the first product step. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

structure FiniteSymmetricChains (I : Type) [Preorder I] (rank : I → ℕ) (K : ℕ) where
  Colour : Type
  finiteColour : Finite Colour
  colour : I → Colour
  start : Colour → ℕ
  start_bound : ∀ c, 2*start c≤K
  rank_bounds : ∀ x, start (colour x)≤rank x ∧ rank x+start (colour x)≤K
  rank_unique : ∀ x y, colour x=colour y → rank x=rank y → x=y
  rank_surjective : ∀ c t, start c≤t → t+start c≤K →
    ∃ x, colour x=c ∧ rank x=t
  chain_le : ∀ x y, colour x=colour y → rank x≤rank y → x≤y

namespace FiniteSymmetricChains

variable {I : Type} [Preorder I] {rank : I → ℕ} {K : ℕ}
    (D : FiniteSymmetricChains I rank K)

instance : Finite D.Colour := D.finiteColour

include D in
/-- Every chain meets the middle layer, and antichains meet each chain
at most once. Both statements refer to the same original finite poset. -/
theorem antichain_card_le_middle [Fintype I] (s : Finset I)
    (hs : IsAntichain (· ≤ ·) (s : Set I)) :
    s.card≤(Finset.univ.filter (fun x => rank x=K/2)).card := by
  letI : Fintype D.Colour := Fintype.ofFinite _
  have hcolour : Function.Injective (fun x : s => D.colour x.val) := by
    intro x y hxy
    apply Subtype.ext
    rcases le_total (rank x.val) (rank y.val) with h|h
    · exact hs.eq x.property y.property (D.chain_le _ _ hxy h)
    · exact hs.eq' x.property y.property (D.chain_le _ _ hxy.symm h)
  have hex (c : D.Colour) : ∃ x, D.colour x=c ∧ rank x=K/2 :=
    D.rank_surjective c (K/2) (by have := D.start_bound c; omega)
      (by have := D.start_bound c; omega)
  let middle : Finset I := Finset.univ.filter (fun x => rank x=K/2)
  let centre : D.Colour → middle := fun c =>
    ⟨(hex c).choose,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hex c).choose_spec.2⟩⟩
  have hcentre : Function.Injective centre := by
    intro c d hcd
    have hv := congrArg (fun x : middle => D.colour x.val) hcd
    change D.colour (hex c).choose=D.colour (hex d).choose at hv
    rw [(hex c).choose_spec.1,(hex d).choose_spec.1] at hv
    exact hv
  have h1 := Fintype.card_le_of_injective _ hcolour
  have h2 := Fintype.card_le_of_injective _ hcentre
  simpa only [Fintype.card_coe] using h1.trans h2

end FiniteSymmetricChains

/-- The explicit rectangle chains have symmetric ranks. -/
def rectangleSymmetricChains (m n : ℕ) :
    FiniteSymmetricChains (Fin m×Fin n) (fun a => a.1.val+a.2.val) (m+n-2) where
  Colour := Fin (min m n)
  finiteColour := inferInstance
  colour := fun a => ⟨RectangleSymmetricChains.colour a,RectangleSymmetricChains.colour_lt a⟩
  start := fun c => c.val
  start_bound := by intro c; have := c.isLt; omega
  rank_bounds := RectangleSymmetricChains.rank_bounds
  rank_unique := by
    intro x y hc hr
    exact RectangleSymmetricChains.same_colour_rank_injective x y (congrArg Fin.val hc) hr
  rank_surjective := by
    intro c t hlo hhi
    obtain ⟨a,ha,har⟩ := RectangleSymmetricChains.rank_surjective c.isLt hlo hhi
    exact ⟨a,Fin.ext ha,har⟩
  chain_le := by
    intro x y hc hr
    rcases RectangleSymmetricChains.same_colour_comparable x y (congrArg Fin.val hc) with h|h
    · exact h
    · have h1 := h.1
      have h2 := h.2
      change x.1≤y.1 ∧ x.2≤y.2
      constructor
      · change x.1.val≤y.1.val
        omega
      · change x.2.val≤y.2.val
        omega

end SymmetricSubgroupAsymptotics
