import SymmetricSubgroupAsymptotics.MarkedC4NilpotentLabelledActions

/-! Concrete ProductEncoding for every actual nilpotent subgroup of S_b.
Both physical degrees, both actual permutation images and all odd choices
are retained in the target; only original-label maps are auxiliary data. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentPhysicalProductEncoding
open NilpotentCompressedImages NilpotentLabelledActions

abbrev Source (b : ℕ) := {K : Subgroup (PermutationGroup b) // Group.IsNilpotent K}
abbrev TargetData (b : ℕ) := Fin (b+1) × Fin (b+1) ×
  Subgroup (Equiv.Perm (Fin (b+1))) × Subgroup (Equiv.Perm (Fin (b+1)))

def supported {b : ℕ} (a : ℕ) (P : Subgroup (Equiv.Perm (Fin (b+1)))) : Prop :=
  ∀ p∈P, ∀ x : Fin (b+1), x.val=0 ∨ a<x.val → p x=x

def Valid {b : ℕ} (z : TargetData b) : Prop :=
  z.1.val+z.2.1.val≤b ∧ IsPGroup 2 z.2.2.1 ∧
    supported z.1.val z.2.2.1 ∧ supported z.2.1.val z.2.2.2 ∧
      Nat.Coprime (Nat.card z.2.2.2) 4
abbrev Target (b : ℕ) := {z : TargetData b // Valid z}

local instance {b : ℕ} (K : Source b) : Group.IsNilpotent K.1 := K.2

def targetCode {b : ℕ} (K : Source b) : Target b := by
  have hbudget := NilpotentCompressedImages.physical_budget K.1 (Fin b)
  rw [Nat.card_fin] at hbudget
  let a : Fin (b+1) := ⟨Nat.card (BinarySupport K.1 (Fin b)),by omega⟩
  let d : Fin (b+1) := ⟨Nat.card (OddSupport K.1 (Fin b)),by omega⟩
  refine ⟨(a,d,(binary K.1).range,(odd K.1).range),hbudget,
    binary_range_isPGroup K.1,?_,?_,odd_range_coprime_four K.1⟩
  · intro p hp x hx
    obtain ⟨g,rfl⟩ := hp
    exact binary_support K.1 g x hx
  · intro o ho x hx
    obtain ⟨g,rfl⟩ := ho
    exact odd_support K.1 g x hx

def code {b : ℕ} (K : Source b) : Target b × PhysicalGridLabels.Code b :=
  (targetCode K,NilpotentOriginalLabels.code K.1)

/-- Both range subgroups and the original-label map recover the ORIGINAL
literal subgroup. This is proved, not supplied as an encoding premise. -/
theorem code_injective (b : ℕ) : Function.Injective (code (b := b)) := by
  intro K L h
  apply Subtype.ext
  apply NilpotentLabelledActions.source_eq K.1
  · exact congrArg (fun z : Target b × PhysicalGridLabels.Code b => z.1.1.2.2.1) h
  · exact congrArg (fun z : Target b × PhysicalGridLabels.Code b => z.1.1.2.2.2) h
  · exact congrArg Prod.snd h

/-- No caller-provided recovery/encoding/Hom-bound data occur here. -/
def encoding (b : ℕ) :
    ProductEncoding (Source b) (Target b) (PhysicalGridLabels.Code b)
      (fun K => K.1) (fun z => z.1.2.2.1) where
  code := code
  code_injective := code_injective b
  hom_card K := hom_card_le_binary_range K.1

/-- Exact finite marked sum over physical-degree-sensitive targets. Odd
configurations remain in Target rather than in the auxiliary alphabet. -/
theorem moment_le (b r : ℕ) :
    (∑ K : Source b, (Nat.card (K.1 →* Multiplicative (ZMod 4)) : ℝ)^r) ≤
      ((b+1 : ℕ)^(3*b) : ℝ) *
      ∑ z : Target b, (Nat.card (z.1.2.2.1 →* Multiplicative (ZMod 4)) : ℝ)^r := by
  have h := (encoding b).homMoment_sum_le r
  rw [PhysicalGridLabels.card_code] at h
  simpa only [Nat.cast_pow] using h
end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentPhysicalProductEncoding
