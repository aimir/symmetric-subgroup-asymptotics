import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Antichain

/-! Explicit symmetric chains in a product of two finite chains. This is
the constructive rectangle step for mixed-prime chain-product width. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RectangleSymmetricChains

/-- Chain c starts at (c,0), rises in the second coordinate to
(c,n-1-c), then rises in the first coordinate. -/
def colour {m n : ℕ} (a : Fin m×Fin n) : ℕ := min a.1.val (n-1-a.2.val)

theorem colour_lt {m n : ℕ} (a : Fin m×Fin n) : colour a<min m n := by
  have hx := a.1.isLt
  have hy := a.2.isLt
  simp only [colour]
  omega

theorem same_colour_comparable {m n : ℕ} (a b : Fin m×Fin n)
    (h : colour a=colour b) : a≤b ∨ b≤a := by
  have ha := a.2.isLt
  have hb := b.2.isLt
  change (a.1≤b.1 ∧ a.2≤b.2) ∨ (b.1≤a.1 ∧ b.2≤a.2)
  change min a.1.val (n-1-a.2.val)=min b.1.val (n-1-b.2.val) at h
  omega

theorem rank_bounds {m n : ℕ} (a : Fin m×Fin n) :
    colour a≤a.1.val+a.2.val ∧ a.1.val+a.2.val+colour a≤m+n-2 := by
  have hx := a.1.isLt
  have hy := a.2.isLt
  simp only [colour]
  omega

theorem same_colour_rank_injective {m n : ℕ} (a b : Fin m×Fin n)
    (hc : colour a=colour b) (hr : a.1.val+a.2.val=b.1.val+b.2.val) : a=b := by
  rcases same_colour_comparable a b hc with hab|hba
  · apply Prod.ext <;> apply Fin.ext
    · have h1 := hab.1; have h2 := hab.2; omega
    · have h1 := hab.1; have h2 := hab.2; omega
  · apply Prod.ext <;> apply Fin.ext
    · have h1 := hba.1; have h2 := hba.2; omega
    · have h1 := hba.1; have h2 := hba.2; omega

/-- Every rank in the symmetric interval [c,m+n-2-c] occurs in chain c. -/
theorem rank_surjective {m n c r : ℕ} (hc : c<min m n)
    (hlo : c≤r) (hhi : r+c≤m+n-2) :
    ∃ a : Fin m×Fin n, colour a=c ∧ a.1.val+a.2.val=r := by
  have hcm : c<m := (lt_min_iff.mp hc).1
  have hcn : c<n := (lt_min_iff.mp hc).2
  by_cases hr : r≤n-1
  · let a : Fin m×Fin n := (⟨c,hcm⟩,⟨r-c,by omega⟩)
    refine ⟨a,?_,?_⟩
    · change min c (n-1-(r-c))=c
      omega
    · change c+(r-c)=r
      omega
  · let a : Fin m×Fin n := (⟨r-(n-1-c),by omega⟩,⟨n-1-c,by omega⟩)
    refine ⟨a,?_,?_⟩
    · change min (r-(n-1-c)) (n-1-(n-1-c))=c
      omega
    · change (r-(n-1-c))+(n-1-c)=r
      omega

/-- Each symmetric chain meets the middle rank in exactly one point. -/
theorem exists_unique_middle {m n c : ℕ} (hc : c<min m n) :
    ∃! a : Fin m×Fin n, colour a=c ∧ a.1.val+a.2.val=(m+n-2)/2 := by
  have hcm := (lt_min_iff.mp hc).1
  have hcn := (lt_min_iff.mp hc).2
  obtain ⟨a,ha,har⟩ := rank_surjective (r := (m+n-2)/2) hc (by omega) (by omega)
  refine ⟨a,⟨ha,har⟩,?_⟩
  intro b hb
  exact same_colour_rank_injective b a (hb.1.trans ha.symm) (hb.2.trans har.symm)

theorem antichain_card_le {m n : ℕ} (s : Finset (Fin m×Fin n))
    (hs : IsAntichain (· ≤ ·) (s : Set (Fin m×Fin n))) : s.card≤min m n := by
  let code : s → Fin (min m n) := fun a => ⟨colour a.val,colour_lt a.val⟩
  have hi : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    have hc : colour a.val=colour b.val := congrArg Fin.val hab
    rcases same_colour_comparable a.val b.val hc with h|h
    · exact hs.eq a.property b.property h
    · exact hs.eq' a.property b.property h
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective code hi

end SymmetricSubgroupAsymptotics.RectangleSymmetricChains
