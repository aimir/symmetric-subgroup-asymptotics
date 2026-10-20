import SymmetricSubgroupAsymptotics.RepresentationSelfDualNestedQuotient

/-!
# Nested quotients are independent of a containing subrepresentation

For `A ≤ B ≤ C` in one ambient representation, the quotient `B / A`
is unchanged if both endpoints are first regarded as subrepresentations of
`C`.  This is the type-level bridge needed by concrete section charts: the
finite certificate uses ambient coordinate states, while a quotient map is
usually defined on the correlated kernel state `C`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

universe u

variable {k G V : Type u} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- The nested copy of `A` in `C` lies in the nested copy of `B` in `C`. -/
theorem nestedSubrepresentation_mono
    {rho : Representation k G V}
    (A B C : Subrepresentation rho)
    (hAB : A ≤ B) (hBC : B ≤ C) :
    nestedSubrepresentation A C (hAB.trans hBC) ≤
      nestedSubrepresentation B C hBC := by
  intro a ha
  exact hAB ha

/-- Forgetting the extra containing subtype is an equivariant equivalence. -/
def nestedSubrepresentationRepresentationEquiv
    {rho : Representation k G V}
    (B C : Subrepresentation rho) (hBC : B ≤ C) :
    B.toRepresentation.Equiv
      (nestedSubrepresentation B C hBC).toRepresentation :=
  Representation.Equiv.mk (nestedSubrepresentationEquiv B C hBC) (by
    intro g
    apply LinearMap.ext
    intro b
    rfl)

/-- The canonical quotient map from the ambient presentation `B/A` to the
same quotient formed after placing both endpoints inside `C`. -/
noncomputable def nestedQuotientAmbientIntertwiner
    {rho : Representation k G V}
    (A B C : Subrepresentation rho)
    (hAB : A ≤ B) (hBC : B ≤ C) :
    (nestedQuotientRepresentation A B hAB).IntertwiningMap
      (nestedQuotientRepresentation
        (nestedSubrepresentation A C (hAB.trans hBC))
        (nestedSubrepresentation B C hBC)
        (nestedSubrepresentation_mono A B C hAB hBC)) where
  toLinearMap :=
    (nestedSubrepresentation A B hAB).toSubmodule.liftQ
      ((nestedSubrepresentation
          (nestedSubrepresentation A C (hAB.trans hBC))
          (nestedSubrepresentation B C hBC)
          (nestedSubrepresentation_mono A B C hAB hBC)).toSubmodule.mkQ.comp
        (nestedSubrepresentationEquiv B C hBC).toLinearMap) (by
          intro a ha
          change (Submodule.Quotient.mk (nestedSubrepresentationEquiv B C hBC a) :
            (nestedSubrepresentation B C hBC).toSubmodule ⧸
              (nestedSubrepresentation
                (nestedSubrepresentation A C (hAB.trans hBC))
                (nestedSubrepresentation B C hBC)
                (nestedSubrepresentation_mono A B C hAB hBC)).toSubmodule) = 0
          rw [Submodule.Quotient.mk_eq_zero]
          exact ha)
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ :=
      (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective x
    rfl

theorem nestedQuotientAmbientIntertwiner_injective
    {rho : Representation k G V}
    (A B C : Subrepresentation rho)
    (hAB : A ≤ B) (hBC : B ≤ C) :
    Function.Injective
      (nestedQuotientAmbientIntertwiner A B C hAB hBC) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ :=
    (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective x
  obtain ⟨b, rfl⟩ :=
    (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective y
  apply (Submodule.Quotient.eq (nestedSubrepresentation A B hAB).toSubmodule).mpr
  change (Submodule.Quotient.mk (nestedSubrepresentationEquiv B C hBC a) :
      (nestedSubrepresentation B C hBC).toSubmodule ⧸
        (nestedSubrepresentation
          (nestedSubrepresentation A C (hAB.trans hBC))
          (nestedSubrepresentation B C hBC)
          (nestedSubrepresentation_mono A B C hAB hBC)).toSubmodule) =
      Submodule.Quotient.mk (nestedSubrepresentationEquiv B C hBC b) at hxy
  have hmem :
      nestedSubrepresentationEquiv B C hBC (a - b) ∈
        (nestedSubrepresentation
          (nestedSubrepresentation A C (hAB.trans hBC))
          (nestedSubrepresentation B C hBC)
          (nestedSubrepresentation_mono A B C hAB hBC)).toSubmodule :=
    by
      simpa only [map_sub] using
        (Submodule.Quotient.eq
          (nestedSubrepresentation
            (nestedSubrepresentation A C (hAB.trans hBC))
            (nestedSubrepresentation B C hBC)
            (nestedSubrepresentation_mono A B C hAB hBC)).toSubmodule).mp hxy
  exact hmem

theorem nestedQuotientAmbientIntertwiner_surjective
    {rho : Representation k G V}
    (A B C : Subrepresentation rho)
    (hAB : A ≤ B) (hBC : B ≤ C) :
    Function.Surjective
      (nestedQuotientAmbientIntertwiner A B C hAB hBC) := by
  intro y
  obtain ⟨c, rfl⟩ :=
    (nestedSubrepresentation
      (nestedSubrepresentation A C (hAB.trans hBC))
      (nestedSubrepresentation B C hBC)
      (nestedSubrepresentation_mono A B C hAB hBC)).toSubmodule.mkQ_surjective y
  let b : B.toSubmodule := ⟨c.1.1, c.2⟩
  refine ⟨Submodule.Quotient.mk b, ?_⟩
  apply (Submodule.Quotient.eq
    (nestedSubrepresentation
      (nestedSubrepresentation A C (hAB.trans hBC))
      (nestedSubrepresentation B C hBC)
      (nestedSubrepresentation_mono A B C hAB hBC)).toSubmodule).mpr
  change nestedSubrepresentationEquiv B C hBC b - c ∈
    (nestedSubrepresentation
      (nestedSubrepresentation A C (hAB.trans hBC))
      (nestedSubrepresentation B C hBC)
      (nestedSubrepresentation_mono A B C hAB hBC)).toSubmodule
  have heq : nestedSubrepresentationEquiv B C hBC b = c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [heq, sub_self]
  exact Submodule.zero_mem _

/-- Canonical equivariant identification of the two quotient
presentations. -/
noncomputable def nestedQuotientAmbientEquiv
    {rho : Representation k G V}
    (A B C : Subrepresentation rho)
    (hAB : A ≤ B) (hBC : B ≤ C) :
    (nestedQuotientRepresentation A B hAB).Equiv
      (nestedQuotientRepresentation
        (nestedSubrepresentation A C (hAB.trans hBC))
        (nestedSubrepresentation B C hBC)
        (nestedSubrepresentation_mono A B C hAB hBC)) :=
  (nestedQuotientAmbientIntertwiner A B C hAB hBC).ofBijective
    ⟨nestedQuotientAmbientIntertwiner_injective A B C hAB hBC,
      nestedQuotientAmbientIntertwiner_surjective A B C hAB hBC⟩

end SymmetricSubgroupAsymptotics

end
