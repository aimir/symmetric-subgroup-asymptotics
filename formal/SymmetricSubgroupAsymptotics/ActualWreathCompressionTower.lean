import SymmetricSubgroupAsymptotics.RelativeCompleteSourceEnvelope
import SymmetricSubgroupAsymptotics.PermutationalWreathElementaryCompression
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
import SymmetricSubgroupAsymptotics.TraceyRefinedAffineInput

/-!
# Iterated compression of an actual wreath embedding

An `ActualWreathCompressionState` keeps one faithful full-component
embedding in the real block system.  Quotienting its local component by a
surjective map constructs the next state: the ambient group is divided by
the literal coordinate intersection, the local group is the displayed
quotient, and the same block top and block set are retained.

`ActualWreathCompressionTower` alternates elementary and semisimple local
chief factors.  Its interpretation is a relative complete-source envelope
whose final faithful action is on the original blocks.  Elementary factors
carry exactly the section-capacity theorem required by the complete Yoneda
incidence; semisimple factors use the proved Scott/subdirect chart.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

universe u

/-- One stage of an actual block-system compression. -/
structure ActualWreathCompressionState
    (Q I : Type) [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I] where
  A : Type
  D : Type
  [groupA : Group A]
  [finiteA : Finite A]
  [groupD : Group D]
  [finiteD : Finite D]
  rho : A →* PermutationalWreathProduct D Q I
  rho_injective : Function.Injective rho
  /-- The faithful permutation degree of the original ambient source.  It is
  retained unchanged through quotient states. -/
  sourceDegree : ℕ
  /-- One padded generating tuple inherited from the original ambient
  permutation group. -/
  generatorCount : ℕ
  generators : Fin generatorCount → A
  generators_full : Subgroup.closure (Set.range generators) = ⊤
  /-- Every prime-character section of the current quotient is still bounded
  by the original faithful permutation degree. -/
  sectionalRank : ∀ (p : ℕ) [Fact p.Prime],
    PrimeSectionalRankBound p A (sourceDegree / p)
  /-- The displayed top is the literal image of the original action on the
  block set.  This is stronger than faithfulness of the abstract `Q`-action
  and is what makes a block stabilizer have index exactly `|I|`. -/
  top_surjective : Function.Surjective
    (PermutationalWreathProduct.rightHom.comp rho)
  top_pretransitive : MulAction.IsPretransitive Q I
  fullComponent :
    PermutationalWreathProduct.Compression.FullComponent rho

attribute [instance]
  ActualWreathCompressionState.groupA
  ActualWreathCompressionState.finiteA
  ActualWreathCompressionState.groupD
  ActualWreathCompressionState.finiteD

namespace ActualWreathCompressionState

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

/-- The literal preimage of a point stabilizer in the displayed top. -/
def topPointStabilizer (S : ActualWreathCompressionState Q I) (i : I) :
    Subgroup S.A :=
  (MulAction.stabilizer Q i).comap
    (PermutationalWreathProduct.rightHom.comp S.rho)

/-- The block stabilizer in every quotient state has the actual number of
blocks as its index.  This was not derivable from `fullComponent` alone; it
uses the retained surjectivity and transitivity of the literal top. -/
theorem topPointStabilizer_index
    (S : ActualWreathCompressionState Q I) (i : I) :
    (S.topPointStabilizer i).index = Fintype.card I := by
  rw [topPointStabilizer,
    Subgroup.index_comap_of_surjective _ S.top_surjective]
  letI : MulAction.IsPretransitive Q I := S.top_pretransitive
  simpa only [Fintype.card_eq_nat_card] using
    MulAction.index_stabilizer_of_transitive Q i

/-- The next literal state after a surjective local compression. -/
def quotient
    (S : ActualWreathCompressionState Q I)
    (D' : Type) [Group D'] [Finite D']
    (phi : S.D →* D') (hphi : Function.Surjective phi) :
    ActualWreathCompressionState Q I where
  A := S.A ⧸ PermutationalWreathProduct.Compression.kernel S.rho phi
  D := D'
  groupA := inferInstance
  finiteA := inferInstance
  groupD := inferInstance
  finiteD := inferInstance
  rho := PermutationalWreathProduct.Compression.quotientEmbedding S.rho phi
  rho_injective :=
    PermutationalWreathProduct.Compression.quotientEmbedding_injective
      S.rho phi
  sourceDegree := S.sourceDegree
  generatorCount := S.generatorCount
  generators := fun i ↦ QuotientGroup.mk'
    (PermutationalWreathProduct.Compression.kernel S.rho phi) (S.generators i)
  generators_full := quotient_generators_full
    (PermutationalWreathProduct.Compression.kernel S.rho phi)
    S.generators S.generators_full
  sectionalRank := by
    intro p hp K
    let q : S.A →* S.A ⧸
        PermutationalWreathProduct.Compression.kernel S.rho phi :=
      QuotientGroup.mk' _
    exact PrimeSectionalRankBound.quotient_rank_le p (S.sectionalRank p)
      (K.comap q) (q.subgroupComap K)
      (q.subgroupComap_surjective_of_surjective K
        (QuotientGroup.mk'_surjective _))
  top_surjective := by
    intro q
    obtain ⟨a, ha⟩ := S.top_surjective q
    refine ⟨QuotientGroup.mk' (PermutationalWreathProduct.Compression.kernel
      S.rho phi) a, ?_⟩
    change (S.rho a).right = q
    exact ha
  top_pretransitive := S.top_pretransitive
  fullComponent :=
    PermutationalWreathProduct.Compression.quotientEmbedding_fullComponent
      S.rho phi hphi S.fullComponent

/-- Projection to the literal top, relabelled only at the final `Fin`
boundary. -/
def terminalAction (S : ActualWreathCompressionState Q I) :
    S.A →* Equiv.Perm (Fin (Fintype.card I)) :=
  (Fintype.equivFin I).permCongrHom.toMonoidHom.comp
    ((MulAction.toPermHom Q I).comp
      (PermutationalWreathProduct.rightHom.comp S.rho))

theorem terminalAction_injective
    (S : ActualWreathCompressionState Q I) (hD : Subsingleton S.D) :
    Function.Injective S.terminalAction := by
  letI : Subsingleton S.D := hD
  intro x y hxy
  apply S.rho_injective
  apply PermutationalWreathProduct.ext
  · funext i
    exact Subsingleton.elim _ _
  · apply (MulAction.toPerm_injective (α := Q) (β := I))
    apply (Fintype.equivFin I).permCongrHom.injective
    exact hxy

end ActualWreathCompressionState

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

/-- A finite actual local-chief compression tower. -/
inductive ActualWreathCompressionTower :
    ActualWreathCompressionState Q I → Type 1 where
  | terminal (S : ActualWreathCompressionState Q I)
      (localTrivial : Subsingleton S.D) :
      ActualWreathCompressionTower S
  | elementary (S : ActualWreathCompressionState Q I)
      (D' : Type) [groupD' : Group D'] [finiteD' : Finite D']
      (phi : S.D →* D') (hphi : Function.Surjective phi)
      (C : ElementaryMinimalNormalChart phi.ker)
      (H : ElementaryLayerJointCapacityBound C.p
        (QuotientGroup.mk'
          (PermutationalWreathProduct.Compression.kernel S.rho phi))
        (QuotientGroup.mk'_surjective
          (PermutationalWreathProduct.Compression.kernel S.rho phi))
        (PermutationalWreathProduct.Compression.kernelElementaryChart
          (p := C.p) S.rho phi C.equiv.symm S.rho_injective).quotientRepresentation
        (PermutationalWreathProduct.Compression.kernelElementaryChart
          (p := C.p) S.rho phi C.equiv.symm S.rho_injective).originalKernelChart)
      (capacity_le_half : H.capacity ≤
        Module.finrank (ZMod C.p) C.V * Fintype.card I / 2)
      (capacity_le_log : H.capacity ≤
        traceyInducedGeneratorCeiling
          (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
      (capacity_refined : TraceyRefinedInducedCapacityBounds C.p
        (Module.finrank (ZMod C.p) C.V) (Fintype.card I) H.capacity)
      (coefficient_le : H.coefficient ≤
        (C.p : ℝ) ^ traceyAffineCoefficientExponent
          (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
          (traceyInducedGeneratorCeiling
            (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
          S.generatorCount S.sourceDegree C.p)
      (next : ActualWreathCompressionTower (S.quotient D' phi hphi)) :
      ActualWreathCompressionTower S
  | semisimple (S : ActualWreathCompressionState Q I)
      (D' : Type) [groupD' : Group D'] [finiteD' : Finite D']
      (phi : S.D →* D') (hphi : Function.Surjective phi)
      (C : SemisimpleNormalChart phi.ker)
      (next : ActualWreathCompressionTower (S.quotient D' phi hphi)) :
      ActualWreathCompressionTower S

namespace ActualWreathCompressionTower

/-- Every elementary exponent in a traced tower comes from an actual natural
tuple length.  The joint-capacity envelope stores that exponent in `ℝ`, so
this predicate retains the integrality which would otherwise be erased. -/
def IntegralCapacities :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → Prop
  | _, .terminal _ _ => True
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact (∃ h : ℕ, H.capacity = h) ∧ IntegralCapacities next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact IntegralCapacities next

/-- Interpret the actual local tower as a complete-source transfer to the
faithful action on the original block set. -/
noncomputable def envelope :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S →
        RelativeCompleteSourceEnvelope S.A
  | S, .terminal _ hD =>
      .identity S.A (Fintype.card I) S.terminalAction
        (S.terminalAction_injective hD)
  | S, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let K := PermutationalWreathProduct.Compression.kernel S.rho phi
      let E := PermutationalWreathProduct.Compression.kernelElementaryChart
        (p := C.p) S.rho phi C.equiv.symm S.rho_injective
      letI : Finite C.V := Finite.of_injective
        (fun v : C.V ↦ C.equiv.symm (Multiplicative.ofAdd v))
        C.equiv.symm.injective
      letI : Finite E.V := by
        change Finite
          (PermutationalWreathProduct.Compression.ElementarySubmodule
            S.rho phi C.equiv.symm)
        exact Finite.of_injective Subtype.val Subtype.val_injective
      letI : Finite E.quotientRepresentation :=
        inferInstanceAs (Finite E.V)
      exact RelativeCompleteSourceEnvelope.elementaryStep (p := C.p)
        K E H next.envelope
  | S, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let K := PermutationalWreathProduct.Compression.kernel S.rho phi
      let E :=
        PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent
          S.rho phi S.rho_injective S.fullComponent C
      exact RelativeCompleteSourceEnvelope.semisimpleStep K E next.envelope

/-- Compression changes the local component but never the actual block set;
the final comparator therefore always has the original number of blocks. -/
theorem envelope_v :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
        T.envelope.v = Fintype.card I
  | _, .terminal _ _ => by
      simp [envelope, RelativeCompleteSourceEnvelope.identity]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [envelope, RelativeCompleteSourceEnvelope.elementaryStep]
        using envelope_v next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [envelope, RelativeCompleteSourceEnvelope.semisimpleStep]
        using envelope_v next

/-- Every actual local-chief tower has nonnegative source exponent.  This is
derived from the literal elementary capacities and is therefore not part of
the numerical input to the affine-component transfer. -/
theorem envelope_eta_nonneg :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) → 0 ≤ T.envelope.eta
  | _, .terminal _ _ => by
      simp [envelope, RelativeCompleteSourceEnvelope.identity]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hp : (1 : ℝ) ≤ C.p := by
        exact_mod_cast C.p_prime.one_le
      have hlog : 0 ≤ Real.logb 2 C.p :=
        Real.logb_nonneg (by norm_num) hp
      have hterm : 0 ≤ Real.logb 2 C.p / C.p * H.capacity := by
        exact mul_nonneg (div_nonneg hlog (by positivity)) H.capacity_nonneg
      simpa only [envelope, RelativeCompleteSourceEnvelope.elementaryStep]
        using add_nonneg hterm (envelope_eta_nonneg next)
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [envelope, RelativeCompleteSourceEnvelope.semisimpleStep]
        using envelope_eta_nonneg next

end ActualWreathCompressionTower
end SymmetricSubgroupAsymptotics

end
