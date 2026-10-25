import SymmetricSubgroupAsymptotics.PartitionFourHeadLargeParts

/-! An explicit code for every partition: four bounded multiplicities
and one separated-cut set. The total mass of the large composition is
recovered from the original partition total and the four heads. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PartitionFiveSeparatedEncoding
open PartitionFourHeadLargeParts FiveSeparatedCompositionStarts FiveSeparatedCutCardinality

def boundedHeads {n : ℕ} (p : Nat.Partition n) : Fin 4 → Fin (n + 1) :=
  fun i => ⟨headCounts p i,Nat.lt_succ_of_le (headCounts_le p i)⟩

def partitionCode {n : ℕ} (p : Nat.Partition n) :
    (Fin 4 → Fin (n + 1)) × SeparatedCuts n :=
  (boundedHeads p,separatedStarts n (largeComposition p) (largeComposition_ge_five p))

private theorem blocks_eq_of_starts_eq {s t : ℕ} (n : ℕ)
    (c : Composition s) (d : Composition t) (hm : s = t) (hs : s ≤ n)
    (he : startCuts n c = startCuts n d) : c.blocks = d.blocks := by
  cases hm
  exact congrArg Composition.blocks (composition_eq_of_startCuts_eq n c d hs he)

theorem partitionCode_injective (n : ℕ) :
    Function.Injective (@partitionCode n) := by
  intro p q he
  have hheads : boundedHeads p = boundedHeads q := congrArg Prod.fst he
  have hh : headCounts p = headCounts q := by
    funext i
    exact congrArg Fin.val (congrFun hheads i)
  have hm := largeMass_eq_of_headCounts_eq p q hh
  have hcuts : startCuts n (largeComposition p) = startCuts n (largeComposition q) :=
    congrArg (fun z : (Fin 4 → Fin (n + 1)) × SeparatedCuts n => z.2.val) he
  have hb := blocks_eq_of_starts_eq n (largeComposition p) (largeComposition q)
    hm (largeMass_le p) hcuts
  have hl : largeParts p = largeParts q := by
    calc
      largeParts p = ((largeComposition p).blocks : Multiset ℕ) :=
        (largeComposition_parts p).symm
      _ = ((largeComposition q).blocks : Multiset ℕ) :=
        congrArg (fun l : List ℕ => (l : Multiset ℕ)) hb
      _ = largeParts q := largeComposition_parts q
  exact partition_eq_of_heads_and_largeParts p q hh hl

theorem partition_card_le_separated (n : ℕ) :
    Nat.card (Nat.Partition n) ≤ (n + 1) ^ 4 * 6 ^ ((n + 4) / 5) := by
  letI : Finite (SeparatedCuts n) :=
    Finite.of_injective (@cutCode n) (cutCode_injective n)
  have h := Nat.card_le_card_of_injective (@partitionCode n) (partitionCode_injective n)
  have hc : Nat.card ((Fin 4 → Fin (n + 1)) × SeparatedCuts n) =
      (n + 1) ^ 4 * Nat.card (SeparatedCuts n) := by
    rw [Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_fin]
  exact h.trans (hc.trans_le (Nat.mul_le_mul_left _ (separatedCuts_card_le n)))

end SymmetricSubgroupAsymptotics.PartitionFiveSeparatedEncoding
