import SymmetricSubgroupAsymptotics.CFSGPSLTwoPermutationDegree

/-! The three-modulo-four square-scalar refinement applies to the SAME
original PSL2 root and torus. It bounds every proper index by q, using
only simplicity and the actual coset action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoThreeModFourPermutationDegree
open CFSGPSLTwoRootCoordinates MulAction PrimitiveSocleRawStructure
variable {F X : Type} [Field F] [Finite F]

theorem field_card_le_of_root_movement [Finite X] [MulAction (PSL (F:=F)) X]
    (hmod : Nat.card F%4=3) (hmove : ∃x:X,projectiveUpper (1:F) • x≠x) :
    Nat.card F ≤ Nat.card X := by
  apply CFSGSquareScalarPermutationDegree.field_card_le_of_root_movement hmod
    (projectiveUpperHom (F:=F)) (projectiveTorus (F:=F))
  · intro t a
    simpa only [projectiveUpperHom_apply,mul_comm] using projective_torus_conjugation t a
  · exact hmove

theorem field_card_le_proper_index [IsSimpleGroup (PSL (F:=F))]
    (hmod : Nat.card F%4=3) (H : Subgroup (PSL (F:=F))) (hH : H≠⊤) :
    Nat.card F ≤ H.index := by
  change Nat.card F ≤ Nat.card (PSL (F:=F)⧸H)
  apply field_card_le_of_root_movement hmod
  apply CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
  intro he
  exact one_ne_zero (projectiveUpper_injective (F:=F) (he.trans projectiveUpper_zero.symm))

theorem field_card_le_leastProperIndex [IsSimpleGroup (PSL (F:=F))]
    (hmod : Nat.card F%4=3) (ell : ℕ) (hell : LeastProperIndex (PSL (F:=F)) ell) :
    Nat.card F ≤ ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact field_card_le_proper_index hmod H hH

end SymmetricSubgroupAsymptotics.CFSGPSLTwoThreeModFourPermutationDegree
