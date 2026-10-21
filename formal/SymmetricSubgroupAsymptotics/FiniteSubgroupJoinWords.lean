import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import Mathlib.Data.Fin.Tuple.Basic

/-! Ordinary words certify exact joins of two displayed generator tuples.
No subgroup-cardinality comparison is used. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

variable {G : Type*} [Group G] {n m q : ℕ}

theorem sup_eq_of_words (left : Fin n → G) (right : Fin m → G)
    (target : Fin q → G)
    (C : FiniteGeneratorEquivWordCertificate (MulEquiv.refl G)
      (Fin.addCases left right) target) :
    Subgroup.closure (Set.range left) ⊔ Subgroup.closure (Set.range right) =
      Subgroup.closure (Set.range target) := by
  have hrange : Set.range (Fin.addCases left right) =
      Set.range left ∪ Set.range right := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · exact Or.inl ⟨j, by simp only [Fin.addCases_left]⟩
      · exact Or.inr ⟨j, by simp only [Fin.addCases_right]⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Fin.castAdd m i, by simp⟩
      · exact ⟨Fin.natAdd n i, by simp⟩
  have h := C.map_closure_eq
  change (Subgroup.closure (Set.range (Fin.addCases left right))).map
    (MonoidHom.id G) = Subgroup.closure (Set.range target) at h
  rw [Subgroup.map_id, hrange, Subgroup.closure_union] at h
  exact h

end SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

end
