import SymmetricSubgroupAsymptotics.FiniteConjugacyCover
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T35

/-! A sparse class-count upper bound for the literal original 8T35 action.
Completeness comes from its checked original row equivalence. Each conjugator
is a row of that same group. The generated data supplies only original-point
equations; no stored conjugacy partition or class count is a premise.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryConjugacyClass8T35

abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley8T35.generators)

local instance conjugacySourceGroup : Group (FiniteGroupRow 128) :=
  BinaryMenuCayley8T35.group

def rows (i : Fin 128) : Original :=
  BinaryMenuCayley8T35.originalEquiv (FiniteGroupRow.mk i)

theorem rows_complete : Function.Surjective rows := by
  intro g
  obtain ⟨i, hi⟩ := BinaryMenuCayley8T35.originalEquiv.surjective g
  exact ⟨i.index, hi⟩

theorem rows_apply (i : Fin 128) (x : Fin 8) :
    (rows i : Equiv.Perm (Fin 8)) x = BinaryConjugacyData8T35.image i x := by
  have hc : permutationCode (rows i : Equiv.Perm (Fin 8)) =
      BinaryMenuCayley8T35.certificate.rows i := by
    change (permutationGeneratorEncoding BinaryMenuCayley8T35.generators).encode
      (BinaryMenuCayley8T35.certificate.toCayley.elements i) = _
    exact BinaryMenuCayley8T35.certificate.encode_elements i
  have h := congrArg (fun c : Fin (8^8) => finFunctionFinEquiv.symm c x) hc
  simpa only [permutationCode, Equiv.symm_apply_apply,
    BinaryConjugacyData8T35.image] using h

def cover : FiniteConjugacyCover rows BinaryConjugacyData8T35.representativeCount := by
  refine FiniteConjugacyCover.ofInjectiveMap rows rows_complete Original.subtype
    Subtype.val_injective BinaryConjugacyData8T35.representative
    BinaryConjugacyData8T35.label BinaryConjugacyData8T35.conjugator ?_
  intro i
  apply Equiv.ext
  intro x
  change (rows (BinaryConjugacyData8T35.conjugator i) : Equiv.Perm (Fin 8))
      ((rows i : Equiv.Perm (Fin 8)) x) =
    (rows (BinaryConjugacyData8T35.representative (BinaryConjugacyData8T35.label i)) :
      Equiv.Perm (Fin 8))
      ((rows (BinaryConjugacyData8T35.conjugator i) : Equiv.Perm (Fin 8)) x)
  simp only [rows_apply]
  exact BinaryConjugacyData8T35.conjugates_pointwise i x

theorem class_card_le_twenty_five : Nat.card (ConjClasses Original) ≤ 25 :=
  cover.card_conjClasses_le_of_le
    BinaryConjugacyData8T35.representativeCount_le_twenty_five

end SymmetricSubgroupAsymptotics.BinaryConjugacyClass8T35

end
