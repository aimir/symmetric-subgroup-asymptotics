import SymmetricSubgroupAsymptotics.FiniteSelfDualNestedQuotientGenerator
import SymmetricSubgroupAsymptotics.BinaryNestedQuotientNonfixedCertificate

/-!
# Finite nested-quotient tables with fixed-layer descent

The finite test for a nested pair may give a reversed cyclic child, a
dimension jump at most two, or a smaller intermediate state containing all
displacements of the upper state. Induction on its dimension then constructs
a nonfixed certificate. This is one uniform proof for every pair in every
registry; the number of fixed upper layers need not be prescribed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G V I : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {rho : Representation (ZMod 2) G V}
  {states : I → Subrepresentation rho}
  (C : BinaryInvariantCyclicOrbitRegistry rho states)
  (e : rho.Equiv rho.dual)

/-- Finite data supporting cyclic, small, and fixed-upper-layer steps.
The strict dimension decrease makes every chain terminate. -/
structure FiniteBinaryNestedQuotientNonfixedData : Type 1 where
  orthogonalState : I → I
  orthogonalState_eq : ∀ i,
    selfDualOrthogonalSubrepresentation rho e (states i) =
      states (orthogonalState i)
  stateDimension : I → ℕ
  state_finrank : ∀ i,
    Module.finrank (ZMod 2) (states i).toSubmodule = stateDimension i
  displacementState : I → I
  displacement_mem : ∀ j g v, v ∈ states j →
    rho g v - v ∈ states (displacementState j)
  step : ∀ i j, states i ≤ states j →
    (∃ c : C.Cyclic, C.child (orthogonalState j) c = orthogonalState i) ∨
    stateDimension j ≤ stateDimension i + 2 ∨
    ∃ k, states i ≤ states k ∧ states k ≤ states j ∧
      states (displacementState j) ≤ states k ∧
      stateDimension k < stateDimension j

namespace FiniteBinaryNestedQuotientNonfixedData

variable (D : FiniteBinaryNestedQuotientNonfixedData C e)

include D

/-- Reversing a cyclic child through self-duality makes the original
nested quotient dual cyclic. -/
theorem dual_generated_of_child (i j : I) (hij : states i ≤ states j)
    (c : C.Cyclic) (hc : C.child (D.orthogonalState j) c = D.orthogonalState i) :
    RepresentationGeneratedBy
      (nestedQuotientRepresentation (states i) (states j) hij).dual 1 := by
  let horth := selfDualOrthogonalSubrepresentation_antitone rho e hij
  have hstate : states (D.orthogonalState j) ≤ states (D.orthogonalState i) := by
    rw [← D.orthogonalState_eq, ← D.orthogonalState_eq]
    exact horth
  have transport (A B A' B' : Subrepresentation rho)
      (hA : A = A') (hB : B = B') (hAB : A ≤ B) (hA'B' : A' ≤ B')
      (hgen : RepresentationGeneratedBy (nestedQuotientRepresentation A B hAB) 1) :
      RepresentationGeneratedBy (nestedQuotientRepresentation A' B' hA'B') 1 := by
    subst A'
    subst B'
    exact hgen
  have hchild : states (D.orthogonalState j) ≤
      states (C.child (D.orthogonalState j) c) := by
    intro x hx
    change x ∈ (states (C.child (D.orthogonalState j) c)).toSubmodule
    rw [C.child_eq]
    exact Submodule.mem_sup_left hx
  have hgenerated : RepresentationGeneratedBy
      (nestedQuotientRepresentation (states (D.orthogonalState j))
        (states (D.orthogonalState i)) hstate) 1 :=
    transport _ _ _ _ rfl (congrArg states hc) hchild hstate
      (C.childQuotientRepresentation_generated (D.orthogonalState j) c)
  have hgeneratedOrth : RepresentationGeneratedBy
      (nestedQuotientRepresentation
        (selfDualOrthogonalSubrepresentation rho e (states j))
        (selfDualOrthogonalSubrepresentation rho e (states i)) horth) 1 :=
    transport _ _ _ _ (D.orthogonalState_eq j).symm
      (D.orthogonalState_eq i).symm hstate horth hgenerated
  let E := selfDualNestedQuotientEquiv rho e (states i) (states j) hij
  exact representationGeneratedBy_of_surjective
    _ _ E.toIntertwiningMap E.surjective hgeneratedOrth

/-- Strong induction converts the finite step table into terminating
derivations for all nested pairs. -/
theorem certificate (i j : I) (hij : states i ≤ states j) :
    BinaryNestedQuotientNonfixedCertificate rho (states i) (states j) hij := by
  generalize hd : D.stateDimension j = n
  induction n using Nat.strong_induction_on generalizing j with
  | h n ih =>
    rcases D.step i j hij with ⟨c, hc⟩ | hsmall | ⟨k, hik, hkj, hdisp, hlt⟩
    · exact .cyclic _ _ _ (D.dual_generated_of_child C e i j hij c hc)
    · apply BinaryNestedQuotientNonfixedCertificate.small
      change Module.finrank (ZMod 2)
        ((states j).toSubmodule ⧸
          (nestedSubrepresentation (states i) (states j) hij).toSubmodule) ≤ 2
      have hquot := (nestedSubrepresentation (states i) (states j)
        hij).toSubmodule.finrank_quotient_add_finrank
      rw [finrank_nestedSubrepresentation, D.state_finrank, D.state_finrank] at hquot
      omega
    · exact .fixedExtension _ _ _ hik hkj
        (fun g v hv ↦ hdisp (D.displacement_mem j g v hv))
        (ih (D.stateDimension k) (by omega) k hik rfl)

/-- Completeness supplies the finite indices for an arbitrary invariant
nested quotient. -/
theorem subrepresentation_certificate [Finite V]
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    BinaryNestedQuotientNonfixedCertificate rho A B hAB := by
  obtain ⟨i, rfl⟩ := C.complete A
  obtain ⟨j, rfl⟩ := C.complete B
  exact D.certificate C e i j hAB

end FiniteBinaryNestedQuotientNonfixedData
end SymmetricSubgroupAsymptotics

end
