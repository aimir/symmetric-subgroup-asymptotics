import SymmetricSubgroupAsymptotics.Axiom69NativeMatrixDefinitionPort
import SymmetricSubgroupAsymptotics.MatrixSeedMonoidUnitsEquivalence
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith

/-! Shared mode-one semantic decoder bridge. Each concrete source needs
ONE equality of its parsed digit list with its native row-major entries,
rather than a full-string reduction for every matrix coordinate. The input
is actual finite source data, not a group equivalence or capacity premise.
No ASCII/Unicode identification is assumed: the entry-list equality itself
relates the new character decoder to the old literal UTF8-byte formula. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Axiom69ModeOneDecoderSemantics
open Axiom69NativeMatrixDefinitionPort

/-- Exactly the mode-one branch of the ported decoder, computed once. -/
def modeOneEntries (s : String) : List ℕ :=
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  (body.filter fun c => !asciiWhitespace c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

/-- Exactly the old MatrixData byte-decoding formula before its ZMod cast. -/
def nativeEntry (rows : Array String) (i j : ℕ) : ℕ :=
  (rows[i]!.toUTF8[j]!).toNat - 48

/-- A row-major list of the actual native coefficient entries. -/
def expectedEntries (n : ℕ) (rows : Array String) : List ℕ :=
  List.ofFn fun k : Fin (n * n) => nativeEntry rows (k.val / n) (k.val % n)

theorem decode_mode_one_apply (p n : ℕ) (s : String) (i j : Fin n) :
    decode p n 1 s i j = ((modeOneEntries s)[i.val * n + j.val]?.getD 0 : ZMod p) := by
  rfl

/-- One parsed-list identity implies every actual matrix coordinate.
The row/column index calculation is wholly symbolic, for arbitrary n. -/
theorem matrix_eq_of_entries (p n : ℕ) (s : String) (rows : Array String)
    (hentries : modeOneEntries s = expectedEntries n rows) :
    decode p n 1 s = CFSG.Models.MatrixData.matrix p n rows := by
  funext i j
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hmul : (i.val + 1) * n ≤ n * n :=
    Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
  have hlt : i.val * n + j.val < n * n := by
    nlinarith [j.isLt]
  have hdiv : (i.val * n + j.val) / n = i.val := by
    rw [Nat.mul_comm i.val n, Nat.mul_add_div hn,
      Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hmod : (i.val * n + j.val) % n = j.val :=
    Nat.mul_add_mod_of_lt j.isLt
  have hlookup : (modeOneEntries s)[i.val * n + j.val]? =
      some (nativeEntry rows i.val j.val) := by
    rw [hentries]
    simp only [expectedEntries, List.getElem?_ofFn, dif_pos hlt]
    change some (nativeEntry rows ((i.val * n + j.val) / n)
      ((i.val * n + j.val) % n)) = some (nativeEntry rows i.val j.val)
    rw [hdiv, hmod]
  change ((modeOneEntries s)[i.val * n + j.val]?.getD 0 : ZMod p) =
    (nativeEntry rows i.val j.val : ZMod p)
  rw [hlookup]
  rfl

/-- Semantic decoder matching feeds the already proved finite-monoid
isomorphism. No upstream model recognition or invertibility is assumed. -/
def equiv_of_entryLists (p n : ℕ) [NeZero p] (a b : Array String)
    (s₁ s₂ : String)
    (h₁ : modeOneEntries s₁ = expectedEntries n a)
    (h₂ : modeOneEntries s₂ = expectedEntries n b) :
    (seedMonoid p n 1 s₁ s₂)ˣ ≃* CFSG.Models.MatrixData.Model p n a b :=
  MatrixSeedMonoidUnitsEquivalence.equiv_of_decoded_eq p n a b
    (decode p n 1 s₁) (decode p n 1 s₂)
    (matrix_eq_of_entries p n s₁ a h₁) (matrix_eq_of_entries p n s₂ b h₂)

end SymmetricSubgroupAsymptotics.Axiom69ModeOneDecoderSemantics
