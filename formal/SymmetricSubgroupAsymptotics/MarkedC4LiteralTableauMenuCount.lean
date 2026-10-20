import SymmetricSubgroupAsymptotics.MarkedC4LiteralWordTableaux
import SymmetricSubgroupAsymptotics.MarkedC4FiniteMonotoneChainCount
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm

/-! Actual normal-tableau menu cost for physical bounded words.
The finite-row injection is applied to actual subgroup partial orders.
The deliberately coarse constant 2^(C!) depends ONLY on the cutoff C. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.LiteralTableauMenuCount
open FiniteOrbitWordShapes FiniteBinaryWordTargets FiniteMonotoneChainCount

variable {C b : ℕ} (T : Target C b)

def RowMenu := ∀ i : Fin T.shape.length.val,
  Chain T.shape.length.val (Subgroup (T.letters i))
instance : Fintype (RowMenu T) := by unfold RowMenu; infer_instance

/-- The original upper tableau actually belongs to the counted menu. -/
def actualUpper : RowMenu T := fun i =>
  ⟨fun j => LiteralWordTableaux.upper T i j.val,
    fun _ _ h => LiteralWordTableaux.upper_mono T i h⟩

/-- The original lower tableau actually belongs to the SAME counted menu. -/
def actualLower : RowMenu T := fun i =>
  ⟨fun j => LiteralWordTableaux.lower T i j.val,
    fun _ _ h => LiteralWordTableaux.lower_mono T i h⟩

private theorem letter_card_le (i : Fin T.shape.length.val) :
    Fintype.card (T.letters i) ≤ C.factorial := by
  have h := Fintype.card_le_of_injective
    (fun x : T.letters i => (x : Equiv.Perm (Fin (T.shape.degrees i).val)))
    Subtype.val_injective
  rw [Fintype.card_perm,Fintype.card_fin] at h
  exact h.trans (Nat.factorial_le (T.shape.degrees i).isLt.le)

/-- All normal-subgroup menus are bounded by all subsets of the same
actual factor. No subgroup census or normal-enumeration certificate occurs. -/
theorem subgroup_menu_le (i : Fin T.shape.length.val) :
    Fintype.card (Subgroup (T.letters i)) ≤ 2^C.factorial := by
  have h := Fintype.card_le_of_injective
    (fun J : Subgroup (T.letters i) => (J : Set (T.letters i))) SetLike.coe_injective
  rw [Fintype.card_set] at h
  exact h.trans (pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) (letter_card_le T i))

/-- This is the genuine O_C(t log t) pre-enumeration factor. The much larger
bound for arbitrary arrays would have incorrectly paid quadratic entropy. -/
theorem card_rowMenu_le : Fintype.card (RowMenu T) ≤
    (T.shape.length.val+1)^((2^C.factorial)*T.shape.length.val) := by
  change Fintype.card (∀ i : Fin T.shape.length.val,
    Chain T.shape.length.val (Subgroup (T.letters i))) ≤ _
  rw [Fintype.card_pi]
  calc
    (∏ i : Fin T.shape.length.val,
      Fintype.card (Chain T.shape.length.val (Subgroup (T.letters i)))) ≤
        ∏ _i : Fin T.shape.length.val,(T.shape.length.val+1)^(2^C.factorial) := by
      apply Finset.prod_le_prod'
      intro i _
      exact (card_chain_le _ _).trans
        (pow_le_pow_right₀ (by omega : 1 ≤ T.shape.length.val+1) (subgroup_menu_le T i))
    _ = ((T.shape.length.val+1)^(2^C.factorial))^T.shape.length.val := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ = (T.shape.length.val+1)^((2^C.factorial)*T.shape.length.val) :=
      (pow_mul _ _ _).symm

end SymmetricSubgroupAsymptotics.MarkedC4.LiteralTableauMenuCount
