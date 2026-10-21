import SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The actual PSL2 torus identifies the square-scalar fixed counts in
the original root action. Every proper coset action of simple PSL2
therefore has degree at least half the original field cardinality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open CFSGPSLTwoRootCoordinates MulAction
variable {F X : Type*} [Field F] [Finite F]

theorem field_card_le_twice_of_root_movement [Finite X]
    [MulAction (PSL (F:=F)) X]
    (hmove : ∀ a : Fˣ, ∃ x : X, projectiveUpper (a : F) • x≠x) :
    Nat.card F≤2*Nat.card X := by
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype X := Fintype.ofFinite X
  letI : MulAction (Multiplicative F) X :=
    MulAction.compHom X (projectiveUpperHom (F:=F))
  apply CFSGSquareScalarPermutationDegree.card_le_twice_of_square_fixedBy
  · intro a c
    have he := Nat.card_congr
      (CFSGConjugateSubgroupDegree.fixedByConjugateEquiv (X:=X)
        (projectiveUpper (F:=F) (a : F)) (projectiveTorus (F:=F) c))
    rw [projective_torus_conjugation] at he
    simpa only [MulAction.fixedBy,MulAction.compHom_smul_def,
      projectiveUpperHom_apply,mul_comm] using he.symm
  · exact hmove

theorem field_card_le_twice_proper_index [IsSimpleGroup (PSL (F:=F))]
    (H : Subgroup (PSL (F:=F))) (hH : H≠⊤) : Nat.card F≤2*H.index := by
  change Nat.card F≤2*Nat.card (PSL (F:=F) ⧸ H)
  apply field_card_le_twice_of_root_movement
  intro a
  apply CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
  intro he
  apply a.ne_zero
  apply projectiveUpper_injective (F:=F)
  exact he.trans projectiveUpper_zero.symm

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry

namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open CFSGPSLTwoRootCoordinates PrimitiveSocleRawStructure
variable {F : Type} [Field F] [Finite F] [IsSimpleGroup (PSL (F:=F))]

theorem field_card_le_twice_leastProperIndex (ell : ℕ)
    (hell : LeastProperIndex (PSL (F:=F)) ell) : Nat.card F≤2*ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact field_card_le_twice_proper_index H hH

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
