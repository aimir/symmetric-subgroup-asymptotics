import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Antichain

/-! An explicit seven-chain partition of the ternary three-cube, and
the resulting bound for componentwise antichains in larger ternary grids.
The fibre-copy theorem assumes an actual antichain labelling; it does not
assert that module heads or leading terms provide such a labelling. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The seven fibres are the chains
`000,100,200,210,220,221,222`; `001,101,201,211,212`;
`002,102,202`; `010,110,120,121,122`; `011,111,112`;
`012`; and `020,021,022`. -/
def ternaryCubeChainColor (a : Fin 3 → Fin 3) : Fin 7 :=
  (![![![0, 1, 2], ![3, 4, 5], ![6, 6, 6]],
     ![![0, 1, 2], ![3, 4, 4], ![3, 3, 3]],
     ![![0, 1, 2], ![0, 1, 1], ![0, 0, 0]]] :
       Fin 3 → Fin 3 → Fin 3 → Fin 7) (a 0) (a 1) (a 2)

set_option maxRecDepth 4096 in
/-- This finite certificate checks all 27 points and all pairs of points.
It uses ordinary kernel reduction, not native evaluation. -/
theorem ternaryCube_sameColor_comparable :
    ∀ a b : Fin 3 → Fin 3, ternaryCubeChainColor a = ternaryCubeChainColor b →
      a ≤ b ∨ b ≤ a := by
  change ∀ a b : Fin 3 → Fin 3, ternaryCubeChainColor a = ternaryCubeChainColor b →
    (∀ i, a i ≤ b i) ∨ (∀ i, b i ≤ a i)
  decide

/-- Every colour class is a chain for componentwise comparison. -/
theorem ternaryCube_color_isChain (c : Fin 7) :
    IsChain (· ≤ ·) {a : Fin 3 → Fin 3 | ternaryCubeChainColor a = c} := by
  intro a ha b hb _
  exact ternaryCube_sameColor_comparable a b (ha.trans hb.symm)

theorem ternaryCube_antichain_card_le_seven
    (s : Finset (Fin 3 → Fin 3))
    (hs : IsAntichain (· ≤ ·) (s : Set (Fin 3 → Fin 3))) :
    s.card ≤ 7 := by
  classical
  have hi : Function.Injective (fun a : s => ternaryCubeChainColor a.1) := by
    intro a b h
    apply Subtype.ext
    rcases ternaryCube_sameColor_comparable a.1 b.1 h with hab | hba
    · exact hs.eq a.2 b.2 hab
    · exact hs.eq' a.2 b.2 hba
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective _ hi

/-- If the final coordinates agree, comparison of the first three
coordinates extends to comparison of the full grid points. -/
theorem ternaryGrid_le_of_firstThree_le {n : ℕ}
    (a b : Fin (3 + n) → Fin 3)
    (hfirst : (fun i : Fin 3 => a (Fin.castAdd n i)) ≤
      (fun i : Fin 3 => b (Fin.castAdd n i)))
    (htail : (fun i : Fin n => a (Fin.natAdd 3 i)) =
      (fun i : Fin n => b (Fin.natAdd 3 i))) : a ≤ b := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    exact hfirst j
  · intro j
    exact le_of_eq (congrFun htail j)

/-- A family whose grid points are pairwise incomparable within each
fibre injects into fibre × seven colours × the remaining coordinates.
The hypothesis also excludes duplicate labels. -/
theorem ternaryGrid_fibre_antichain_card_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] (n : ℕ) (fibre : ι → κ)
    (point : ι → Fin (3 + n) → Fin 3)
    (hsep : ∀ i j, fibre i = fibre j → point i ≤ point j → i = j) :
    Fintype.card ι ≤ Fintype.card κ * (7 * 3 ^ n) := by
  let code (i : ι) : κ × (Fin 7 × (Fin n → Fin 3)) :=
    (fibre i, ternaryCubeChainColor (fun a => point i (Fin.castAdd n a)),
      fun a => point i (Fin.natAdd 3 a))
  have hi : Function.Injective code := by
    intro i j hij
    have hf : fibre i = fibre j := congrArg Prod.fst hij
    have hc : ternaryCubeChainColor (fun a => point i (Fin.castAdd n a)) =
        ternaryCubeChainColor (fun a => point j (Fin.castAdd n a)) :=
      congrArg (fun x : κ × (Fin 7 × (Fin n → Fin 3)) => x.2.1) hij
    have ht : (fun a : Fin n => point i (Fin.natAdd 3 a)) =
        (fun a : Fin n => point j (Fin.natAdd 3 a)) :=
      congrArg (fun x : κ × (Fin 7 × (Fin n → Fin 3)) => x.2.2) hij
    rcases ternaryCube_sameColor_comparable _ _ hc with h | h
    · exact hsep i j hf (ternaryGrid_le_of_firstThree_le _ _ h ht)
    · exact (hsep j i hf.symm (ternaryGrid_le_of_firstThree_le _ _ h ht.symm)).symm
  simpa only [Fintype.card_prod, Fintype.card_pi_const, Fintype.card_fin] using
    Fintype.card_le_of_injective code hi

/-- The product-slice bound, with the number of remaining coordinates
written directly as `n`. -/
theorem ternaryGrid_antichain_card_le (n : ℕ)
    (s : Finset (Fin (3 + n) → Fin 3))
    (hs : IsAntichain (· ≤ ·) (s : Set (Fin (3 + n) → Fin 3))) :
    s.card ≤ 7 * 3 ^ n := by
  classical
  have h := ternaryGrid_fibre_antichain_card_le n
    (fun _ : s => (PUnit.unit : PUnit.{1}))
    (fun a : s => a.1) (fun a b _ hab => Subtype.ext (hs.eq a.2 b.2 hab))
  simpa only [Fintype.card_coe, Fintype.card_punit, one_mul] using h

/-- Every componentwise antichain in the ternary t-grid, t ≥ 3, meets
at most seven chains in each fixed-tail slice. -/
theorem ternaryGrid_antichain_card_le_of_three_le (t : ℕ) (ht : 3 ≤ t)
    (s : Finset (Fin t → Fin 3))
    (hs : IsAntichain (· ≤ ·) (s : Set (Fin t → Fin 3))) :
    s.card ≤ 7 * 3 ^ (t - 3) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  simpa only [Nat.add_sub_cancel_left] using ternaryGrid_antichain_card_le n s hs

/-- Finite fibre copies multiply the same bound. No linear algebra or
group-action hypotheses are hidden in this combinatorial statement. -/
theorem ternaryGrid_fibre_antichain_card_le_of_three_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] (t : ℕ) (ht : 3 ≤ t) (fibre : ι → κ)
    (point : ι → Fin t → Fin 3)
    (hsep : ∀ i j, fibre i = fibre j → point i ≤ point j → i = j) :
    Fintype.card ι ≤ Fintype.card κ * (7 * 3 ^ (t - 3)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  simpa only [Nat.add_sub_cancel_left] using
    ternaryGrid_fibre_antichain_card_le n fibre point hsep

end SymmetricSubgroupAsymptotics
