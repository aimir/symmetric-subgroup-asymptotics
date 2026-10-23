import SymmetricSubgroupAsymptotics.BinaryColoredPartitionEncoding
import SymmetricSubgroupAsymptotics.PermutationalWreathFinite
import Mathlib.Data.Finite.Perm

/-! Actual full binary wreath class counts from the constructed colored
cycle conjugators. Two-element coefficients are relabelled bijectively
by Bool; no group identification or class-count formula is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFullWreathClassBound
open PermutationWreathClassData PermutationWreathBaseConjugacy
  BinaryColoredPartitionEncoding BinaryPartitionBudget

def mapColors {D E : Type*} (e : D ↪ E) {n : ℕ}
    (s : ColoredParts D n) : ColoredParts E n :=
  ⟨s.val.map (fun t => (t.1,e t.2)),by
    constructor
    · intro t ht
      obtain ⟨u,hu,rfl⟩ := Multiset.mem_map.mp ht
      exact s.property.1 u hu
    · rw [Multiset.map_map]
      exact s.property.2⟩

theorem mapColors_injective {D E : Type*} (e : D ↪ E) (n : ℕ) :
    Function.Injective (mapColors e : ColoredParts D n → ColoredParts E n) := by
  have hi : Function.Injective (fun t : ℕ × D => (t.1,e t.2)) := by
    intro a b he
    exact Prod.ext (congrArg (fun z : ℕ × E => z.1) he)
      (e.injective (congrArg (fun z : ℕ × E => z.2) he))
  intro s t he
  apply Subtype.ext
  exact Multiset.map_injective hi (congrArg Subtype.val he)

def colorEquivBool (D : Type*) [Finite D] (hD : Nat.card D=2) : D ≃ Bool := by
  letI : Fintype D := Fintype.ofFinite _
  have hc : Fintype.card D=2 := by simpa only [Nat.card_eq_fintype_card] using hD
  exact Fintype.equivOfCardEq (hc.trans (by decide : 2=Fintype.card Bool))

variable {D I : Type*} [CommGroup D] [Finite D] [Finite I]

def classEncoding (hD : Nat.card D=2) :
    ConjClasses (Wreath D I) → PairedPartitions (Nat.card I) :=
  fun c => pairedEncoding (mapColors (colorEquivBool D hD).toEmbedding (classDataMap c))

theorem classEncoding_injective (hD : Nat.card D=2) :
    Function.Injective (classEncoding (I := I) hD) := by
  intro c d he
  apply classDataMap_injective
  apply mapColors_injective (colorEquivBool D hD).toEmbedding (Nat.card I)
  apply pairedEncoding_injective (Nat.card I)
  exact he

theorem class_card_le_pairedPartitions (hD : Nat.card D=2) :
    Nat.card (ConjClasses (Wreath D I))≤Nat.card (PairedPartitions (Nat.card I)) :=
  Nat.card_le_card_of_injective (classEncoding hD) (classEncoding_injective hD)

theorem class_card_le_coarse (hD : Nat.card D=2) :
    Nat.card (ConjClasses (Wreath D I))≤(Nat.card I+1)*2^Nat.card I :=
  (class_card_le_pairedPartitions hD).trans (pairedPartitions_card_le (Nat.card I))

theorem class_cube_le_garonziMaroti (hD : Nat.card D=2) (hI : 7≤Nat.card I) :
    Nat.card (ConjClasses (Wreath D I))^3≤5^(2*Nat.card I-1) :=
  (Nat.pow_le_pow_left (class_card_le_coarse hD) 3).trans
    (coarse_cube_le_garonziMaroti (Nat.card I) hI)

end SymmetricSubgroupAsymptotics.BinaryFullWreathClassBound
