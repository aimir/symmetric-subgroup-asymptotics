import SymmetricSubgroupAsymptotics.FiniteColoredPartitionSplit
import SymmetricSubgroupAsymptotics.BinaryFullWreathClassBound

/-! An explicit reversible encoding of positive colored parts by coupled
partition tuples. The decoder reconstructs the entire original multiset;
the original total is kept at every recursive color split. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteColoredPartitionEncoding
open FiniteColoredPartitionTuple FiniteColoredPartitionSplit

def encode : (k n : ℕ) → Parts k n → Code k n
  | 0,_,s => ⟨zero_weight s⟩
  | k+1,_,s => ⟨headIndex s,headPartition s,encode k _ (tailState s)⟩

def decode : (k n : ℕ) → Code k n → Multiset (ℕ × Fin k)
  | 0,_,_ => 0
  | k+1,n,⟨j,p,t⟩ =>
    (p.parts.map (fun m => (m,(0 : Fin (k+1))))) +
      (decode k (n-j.val) t).map (fun u => (u.1,u.2.succ))

theorem decode_encode (k n : ℕ) (s : Parts k n) :
    decode k n (encode k n s) = s.val := by
  induction k generalizing n with
  | zero => exact (zero_empty s).symm
  | succ k ih =>
    change (headParts s.val).map (fun m => (m,(0 : Fin (k+1)))) +
      (decode k _ (encode k _ (tailState s))).map (fun t => (t.1,t.2.succ)) = s.val
    rw [ih]
    exact reconstruction s.val

theorem encode_injective (k n : ℕ) : Function.Injective (encode k n) := by
  intro s t he
  apply Subtype.ext
  have h := congrArg (decode k n) he
  simpa only [decode_encode] using h

instance finiteParts (k n : ℕ) : Finite (Parts k n) :=
  Finite.of_injective (encode k n) (encode_injective k n)

theorem fin_color_card_le (k n : ℕ) :
    Nat.card (Parts k n) ≤ (n+1)^k * Nat.fib (n+1) :=
  (Nat.card_le_card_of_injective (encode k n) (encode_injective k n)).trans
    (FiniteColoredPartitionTuple.card_le_polynomial_fib k n)

instance finiteColoredParts (T : Type*) [Finite T] (n : ℕ) :
    Finite (PermutationWreathClassData.ColoredParts T n) :=
  Finite.of_injective
    (BinaryFullWreathClassBound.mapColors (Finite.equivFin T).toEmbedding)
    (BinaryFullWreathClassBound.mapColors_injective (Finite.equivFin T).toEmbedding n)

theorem color_card_le (T : Type*) [Finite T] (n : ℕ) :
    Nat.card (PermutationWreathClassData.ColoredParts T n) ≤
      (n+1)^Nat.card T * Nat.fib (n+1) := by
  let e := Finite.equivFin T
  exact (Nat.card_le_card_of_injective
    (BinaryFullWreathClassBound.mapColors e.toEmbedding)
    (BinaryFullWreathClassBound.mapColors_injective e.toEmbedding n)).trans
      (fin_color_card_le (Nat.card T) n)

end SymmetricSubgroupAsymptotics.FiniteColoredPartitionEncoding
