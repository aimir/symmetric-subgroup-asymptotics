import SymmetricSubgroupAsymptotics.FiniteBinaryNestedQuotientNonfixed

/-!
# Finite nested-quotient tables with two-sided fixed-layer descent

A finite step may give a reversed cyclic child, a dimension jump at most
two, a fixed upper layer, or a fixed lower layer. Induction on the difference
of endpoint dimensions handles both kinds of descent. The existing
fixed-upper-only table and its API remain available unchanged.
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

/-- Finite data for cyclic, small, fixed-upper, and fixed-lower steps.
The last two alternatives strictly decrease the quotient dimension. -/
structure FiniteBinaryNestedQuotientTwoSidedData : Type 1 where
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
    (∃ k, states i ≤ states k ∧ states k ≤ states j ∧
      states (displacementState j) ≤ states k ∧
      stateDimension k < stateDimension j) ∨
    ∃ k, states i ≤ states k ∧ states k ≤ states j ∧
      states (displacementState k) ≤ states i ∧
      stateDimension i < stateDimension k

namespace FiniteBinaryNestedQuotientTwoSidedData

variable (D : FiniteBinaryNestedQuotientTwoSidedData C e)

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

/-- State inclusion controls the finite dimension table. -/
theorem stateDimension_mono {i j : I} (hij : states i ≤ states j) :
    D.stateDimension i ≤ D.stateDimension j := by
  rw [← D.state_finrank i, ← D.state_finrank j]
  exact Submodule.finrank_mono hij

/-- Strong induction on the quotient dimension allows either endpoint to
move inward across a fixed layer. -/
theorem certificate (i j : I) (hij : states i ≤ states j) :
    BinaryNestedQuotientNonfixedCertificate rho (states i) (states j) hij := by
  generalize hd : D.stateDimension j - D.stateDimension i = n
  induction n using Nat.strong_induction_on generalizing i j with
  | h n ih =>
    rcases D.step i j hij with
      ⟨c, hc⟩ | hsmall | ⟨k, hik, hkj, hdisp, hlt⟩ | ⟨k, hik, hkj, hdisp, hlt⟩
    · exact .cyclic _ _ _ (D.dual_generated_of_child C e i j hij c hc)
    · apply BinaryNestedQuotientNonfixedCertificate.small
      change Module.finrank (ZMod 2)
        ((states j).toSubmodule ⧸
          (nestedSubrepresentation (states i) (states j) hij).toSubmodule) ≤ 2
      have hquot := (nestedSubrepresentation (states i) (states j)
        hij).toSubmodule.finrank_quotient_add_finrank
      rw [finrank_nestedSubrepresentation, D.state_finrank, D.state_finrank] at hquot
      omega
    · have hdim := D.stateDimension_mono C e hik
      exact .fixedExtension _ _ _ hik hkj
        (fun g v hv ↦ hdisp (D.displacement_mem j g v hv))
        (ih (D.stateDimension k - D.stateDimension i) (by omega) i k hik rfl)
    · have hdim := D.stateDimension_mono C e hkj
      exact .fixedLowerExtension _ _ _ hik hkj
        (fun g v hv ↦ hdisp (D.displacement_mem k g v hv))
        (ih (D.stateDimension j - D.stateDimension k) (by omega) k j hkj rfl)

/-- Completeness supplies endpoints for every invariant nested quotient. -/
theorem subrepresentation_certificate [Finite V]
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    BinaryNestedQuotientNonfixedCertificate rho A B hAB := by
  obtain ⟨i, rfl⟩ := C.complete A
  obtain ⟨j, rfl⟩ := C.complete B
  exact D.certificate C e i j hAB

end FiniteBinaryNestedQuotientTwoSidedData
end SymmetricSubgroupAsymptotics

end
