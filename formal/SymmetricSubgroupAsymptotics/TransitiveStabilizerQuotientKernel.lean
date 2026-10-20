import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! The action on cosets of an actual point stabilizer has exactly the
kernel of the original transitive action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A X : Type} [Group A] [MulAction A X]
    [MulAction.IsPretransitive A X]

/-- Both permutation homomorphisms retain their original acting group. -/
theorem transitive_stabilizer_quotient_kernel (x₀ : X) :
    (MulAction.toPermHom A (A ⧸ MulAction.stabilizer A x₀)).ker =
      (MulAction.toPermHom A X).ker := by
  let f := MulAction.ofQuotientStabilizer A x₀
  have hinj : Function.Injective f := MulAction.injective_ofQuotientStabilizer A x₀
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq A x₀ x
    exact ⟨(a : A ⧸ MulAction.stabilizer A x₀),ha⟩
  ext a
  rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
  constructor
  · intro ha
    apply Equiv.ext
    intro x
    obtain ⟨q,rfl⟩ := hsurj x
    have he := congrArg (fun p : Equiv.Perm (A ⧸ MulAction.stabilizer A x₀) =>
      f (p q)) ha
    change f (a • q) = f q at he
    change MulAction.ofQuotientStabilizer A x₀ (a • q) =
      MulAction.ofQuotientStabilizer A x₀ q at he
    rw [MulAction.ofQuotientStabilizer_smul] at he
    exact he
  · intro ha
    apply Equiv.ext
    intro q
    apply hinj
    change f (a • q) = f q
    change MulAction.ofQuotientStabilizer A x₀ (a • q) =
      MulAction.ofQuotientStabilizer A x₀ q
    rw [MulAction.ofQuotientStabilizer_smul]
    exact congrArg (fun p : Equiv.Perm X => p (f q)) ha

end SymmetricSubgroupAsymptotics
end
