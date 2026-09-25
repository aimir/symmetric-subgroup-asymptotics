import SymmetricSubgroupAsymptotics.TernaryCubeAntichain
import SymmetricSubgroupAsymptotics.TernaryLocalWidth

/-! All ternary grid dimensions, including zero, one and two, with
arbitrary finite fibre copies. The antichain hypothesis remains explicit. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

/-- The three chains are `00,10,20,21,22`; `01,11,12`; and `02`. -/
def ternarySquareChainColor (a : Fin 2 → Fin 3) : Fin 3 :=
  (![![0, 1, 2], ![0, 1, 1], ![0, 0, 0]] : Fin 3 → Fin 3 → Fin 3) (a 0) (a 1)

set_option maxRecDepth 4096 in
theorem ternarySquare_sameColor_comparable :
    ∀ a b : Fin 2 → Fin 3, ternarySquareChainColor a = ternarySquareChainColor b →
      a ≤ b ∨ b ≤ a := by
  change ∀ a b : Fin 2 → Fin 3, ternarySquareChainColor a = ternarySquareChainColor b →
    (∀ i, a i ≤ b i) ∨ (∀ i, b i ≤ a i)
  decide

theorem ternarySquare_fibre_antichain_card_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] (fibre : ι → κ) (point : ι → Fin 2 → Fin 3)
    (hsep : ∀ i j, fibre i = fibre j → point i ≤ point j → i = j) :
    Fintype.card ι ≤ Fintype.card κ * 3 := by
  let code (i : ι) : κ × Fin 3 := (fibre i, ternarySquareChainColor (point i))
  have hi : Function.Injective code := by
    intro i j hij
    have hf : fibre i = fibre j := congrArg Prod.fst hij
    have hc : ternarySquareChainColor (point i) = ternarySquareChainColor (point j) :=
      congrArg Prod.snd hij
    rcases ternarySquare_sameColor_comparable _ _ hc with h | h
    · exact hsep i j hf h
    · exact (hsep j i hf.symm h).symm
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_le_of_injective code hi

/-- An actual antichain labelling in fibre copies of the t-grid obeys
the integer width coefficient in every dimension. This theorem does not
construct a labelling for a representation or its intrinsic head. -/
theorem ternaryGrid_fibre_antichain_card_le_width {ι κ : Type*}
    [Fintype ι] [Fintype κ] (t : ℕ) (fibre : ι → κ)
    (point : ι → Fin t → Fin 3)
    (hsep : ∀ i j, fibre i = fibre j → point i ≤ point j → i = j) :
    Fintype.card ι ≤ Fintype.card κ * ternaryLocalWidth t := by
  by_cases ht : 3 ≤ t
  · rw [ternaryLocalWidth_eq_of_three_le t ht]
    exact ternaryGrid_fibre_antichain_card_le_of_three_le t ht fibre point hsep
  · have hsmall : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases hsmall with rfl | rfl | rfl
    · have hi : Function.Injective fibre := by
        intro i j hij
        exact hsep i j hij (fun x => Fin.elim0 x)
      simpa using Fintype.card_le_of_injective fibre hi
    · have hi : Function.Injective fibre := by
        intro i j hij
        rcases le_total (point i 0) (point j 0) with h | h
        · apply hsep i j hij
          intro x
          simpa only [Fin.eq_zero x] using h
        · apply (hsep j i hij.symm ?_).symm
          intro x
          simpa only [Fin.eq_zero x] using h
      simpa using Fintype.card_le_of_injective fibre hi
    · simpa using ternarySquare_fibre_antichain_card_le fibre point hsep

end SymmetricSubgroupAsymptotics
