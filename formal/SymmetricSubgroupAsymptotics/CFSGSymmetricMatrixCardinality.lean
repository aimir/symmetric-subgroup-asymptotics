import SymmetricSubgroupAsymptotics.CFSGMatrixBlockCell
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Parity

/-! Exact cardinality of literal symmetric matrices, via their entries
on unordered pairs, including the diagonal. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymmetricMatrixCardinality

def SymmetricMatrix (R I : Type*) :=
  {S : Matrix I I R // ∀ i j, S i j = S j i}

def entriesEquiv (R I : Type*) : SymmetricMatrix R I ≃ (Sym2 I → R) := Sym2.lift

theorem symmetricMatrix_card (R I : Type*) [Finite R] [Fintype I] :
    Nat.card (SymmetricMatrix R I) = Nat.card R ^ ((Nat.card I + 1).choose 2) := by
  rw [Nat.card_congr (entriesEquiv R I), Nat.card_fun]
  congr 1
  simpa only [Nat.card_eq_fintype_card] using (Sym2.card (α := I))

theorem twice_choose_two_succ (r : ℕ) : 2 * (r + 1).choose 2 = r * (r + 1) := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have hd : 2 ∣ (r + 1) * r := by
    rw [mul_comm]
    exact Nat.two_dvd_mul_add_one r
  simpa only [mul_comm] using Nat.mul_div_cancel' hd

theorem symmetricMatrix_pair_card (R : Type*) [Finite R] (r : ℕ) :
    Nat.card (SymmetricMatrix R (Fin r) × SymmetricMatrix R (Fin r)) =
      Nat.card R ^ (r * (r + 1)) := by
  rw [Nat.card_prod, symmetricMatrix_card R (Fin r), Nat.card_fin, ← pow_add]
  congr 1
  have h := twice_choose_two_succ r
  omega

theorem transpose_eq {R I : Type*} (S : SymmetricMatrix R I) :
    S.val.transpose = S.val := by
  ext i j
  exact S.property j i

def oppositeCell {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (p : SymmetricMatrix R I × SymmetricMatrix R I) : Matrix (I ⊕ I) (I ⊕ I) R :=
  CFSGMatrixBlockCell.cell 1 p.1.val p.2.val

theorem oppositeCell_injective {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I] :
    Function.Injective (oppositeCell (R := R) (I := I)) := by
  rintro ⟨S, T⟩ ⟨S', T'⟩ h
  have he : ((1 : (Matrix I I R)ˣ), (S.val, T.val)) =
      ((1 : (Matrix I I R)ˣ), (S'.val, T'.val)) :=
    CFSGMatrixBlockCell.cell_injective h
  have hs := congrArg (fun p : (Matrix I I R)ˣ × (Matrix I I R × Matrix I I R) => p.2.1) he
  have ht := congrArg (fun p : (Matrix I I R)ˣ × (Matrix I I R × Matrix I I R) => p.2.2) he
  exact Prod.ext (Subtype.ext hs) (Subtype.ext ht)

theorem oppositeCell_range_card (R : Type*) [CommRing R] [Finite R] (r : ℕ) :
    Nat.card (Set.range (oppositeCell (R := R) (I := Fin r))) =
      Nat.card R ^ (r * (r + 1)) := by
  rw [← Nat.card_congr (Equiv.ofInjective _ oppositeCell_injective)]
  exact symmetricMatrix_pair_card R r

end SymmetricSubgroupAsymptotics.CFSGSymmetricMatrixCardinality
