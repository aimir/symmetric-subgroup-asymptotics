import SymmetricSubgroupAsymptotics.FiniteConjugacyCover
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding

/-! Sparse conjugacy covers for original encoded permutation groups.
The row map and its completeness come from the original Cayley certificate.
Only pointwise equations with conjugators in those same rows are supplied.
No row-group multiplication table or distinctness of representatives is needed. -/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.EncodedCayleyCertificate

variable {w n c : ℕ} {ι : Type*} {generators : ι → Equiv.Perm (Fin w)}
    (C : EncodedCayleyCertificate (permutationGeneratorEncoding generators) n)

def originalPermutationRows (i : Fin n) : Subgroup.closure (Set.range generators) :=
  ⟨C.toCayley.elements i, (C.toCayley.mem_closure_iff _).mpr ⟨i,rfl⟩⟩

theorem originalPermutationRows_surjective :
    Function.Surjective C.originalPermutationRows := by
  intro g
  obtain ⟨i,hi⟩ := (C.toCayley.mem_closure_iff g.val).mp g.property
  exact ⟨i,Subtype.ext hi⟩

theorem originalPermutationRows_apply (i : Fin n) (x : Fin w) :
    (C.originalPermutationRows i : Equiv.Perm (Fin w)) x =
      finFunctionFinEquiv.symm (C.rows i) x := by
  have hc : permutationCode (C.originalPermutationRows i : Equiv.Perm (Fin w)) =
      C.rows i := C.encode_elements i
  have h := congrArg (fun z : Fin (w^w) => finFunctionFinEquiv.symm z x) hc
  simpa only [permutationCode, Equiv.symm_apply_apply] using h

/-- Pointwise original-row witnesses bound the complete original group's
class count, including nonabelian groups and duplicate class labels. -/
theorem permutation_conjClasses_card_le
    (representative : Fin c → Fin n) (label : Fin n → Fin c)
    (conjugator : Fin n → Fin n)
    (hconjugates : ∀ (i : Fin n) (x : Fin w),
      finFunctionFinEquiv.symm (C.rows (conjugator i))
          (finFunctionFinEquiv.symm (C.rows i) x) =
        finFunctionFinEquiv.symm (C.rows (representative (label i)))
          (finFunctionFinEquiv.symm (C.rows (conjugator i)) x)) :
    Nat.card (ConjClasses (Subgroup.closure (Set.range generators))) ≤ c := by
  let cover : FiniteConjugacyCover C.originalPermutationRows c :=
    FiniteConjugacyCover.ofInjectiveMap C.originalPermutationRows
      C.originalPermutationRows_surjective (Subgroup.closure (Set.range generators)).subtype
      Subtype.val_injective representative label conjugator (by
        intro i
        apply Equiv.ext
        intro x
        change (C.originalPermutationRows (conjugator i) : Equiv.Perm (Fin w))
            ((C.originalPermutationRows i : Equiv.Perm (Fin w)) x) =
          (C.originalPermutationRows (representative (label i)) : Equiv.Perm (Fin w))
            ((C.originalPermutationRows (conjugator i) : Equiv.Perm (Fin w)) x)
        simp only [C.originalPermutationRows_apply]
        exact hconjugates i x)
  exact cover.card_conjClasses_le

end SymmetricSubgroupAsymptotics.EncodedCayleyCertificate
