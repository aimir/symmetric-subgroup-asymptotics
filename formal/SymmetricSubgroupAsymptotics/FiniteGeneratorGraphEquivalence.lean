import SymmetricSubgroupAsymptotics.FiniteGeneratorGraphCertificate

/-! A selected quotient graph is an exact group equivalence when both its
literal coordinate projections separate its states. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteGeneratorGraphCertificate
variable {G H I J : Type} [Group G] [Group H]
  {source : J → G} {target : J → H}
  (C : FiniteGeneratorGraphCertificate (I := I) source target)

include C in
theorem hom_injective_of_target_injective
    (hinj : Function.Injective (fun i => (C.state i).2)) :
    Function.Injective C.hom := by
  intro x y h
  obtain ⟨i,rfl⟩ := C.sourceElement_surjective x
  obtain ⟨j,rfl⟩ := C.sourceElement_surjective y
  have he := congrArg Subtype.val h
  rw [C.hom_sourceElement,C.hom_sourceElement] at he
  exact congrArg C.sourceElement (hinj he)

def equiv (hinj : Function.Injective (fun i => (C.state i).2)) :
    C.Source ≃* C.Target :=
  MulEquiv.ofBijective C.hom ⟨C.hom_injective_of_target_injective hinj,C.hom_surjective⟩
end SymmetricSubgroupAsymptotics.FiniteGeneratorGraphCertificate
