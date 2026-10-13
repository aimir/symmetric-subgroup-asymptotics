import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicQuotientGenerator
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads
import SymmetricSubgroupAsymptotics.RepresentationSelfDualNestedQuotient
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopQuotientGeneratorData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops

/-!
# Dual generators for paired-eight state quotients

The eleven invariant states of the paired-eight natural module are closed
under orthogonal complement for the standard coordinate pairing.  Reversing
a nested pair by this involution turns all but three state quotients into
single edges of the checked cyclic child table. The exceptions are the
quotients of states 7, 9 and 10 by state 3. The first has dimension two;
the latter two reduce to a cyclic-dual quotient by removing fixed upper
layers. The resulting nonfixed bound applies to every nested pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators


abbrev Top := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top
abbrev ModelModule := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.ModelModule
abbrev representation := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.representation
abbrev states := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states
abbrev charts := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.charts

/-- State index of the standard-coordinate orthogonal complement. -/
def orthogonalState (i : Fin 11) : Fin 11 :=
  (#[10, 9, 8, 7, 4, 5, 6, 3, 2, 1, 0] : Array (Fin 11))[i.val]!

/-- The permutation-module self-duality is the ordinary coordinate dot
product. -/
theorem selfDual_apply (v w : ModelModule) :
    permutationFunctionRepresentationSelfDual (G := Top) v w =
      ∑ x, v x * w x :=
  permutationFunctionRepresentationSelfDual_apply (G := Top) v w

/-- Testing a linear functional on a coordinate basis suffices for the
whole annihilator. This keeps the finite test linear in the chart dimension. -/
private theorem chart_annihilator_mem_iff {w d : ℕ}
    (C : BinaryCoordinateSpace w d)
    (f : Module.Dual (ZMod 2) (Fin w → ZMod 2)) :
    f ∈ C.space.dualAnnihilator ↔
      ∀ j, f (C.inclusion (Pi.single j 1)) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h j
    exact h _ ⟨Pi.single j 1, rfl⟩
  · intro h v hv
    have hle : C.space ≤ LinearMap.ker f :=
      C.le_of_basis_mem _ (fun j ↦ h j)
    exact hle hv

/-- Literal orthogonal-complement table for all eleven invariant states. -/
theorem orthogonalState_eq (i : Fin 11) :
    selfDualOrthogonalSubrepresentation representation
        permutationFunctionRepresentationSelfDual (states i) =
      states (orthogonalState i) := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change (permutationFunctionRepresentationSelfDual (G := Top) v ∈
      (states i).toSubmodule.dualAnnihilator) ↔
    v ∈ (states (orthogonalState i)).toSubmodule
  rw [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space, SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space, chart_annihilator_mem_iff]
  simp only [selfDual_apply]
  fin_cases i <;> decide +kernel +revert

/-- Exactly three nested pairs need more than a single reversed child
edge. Their small or fixed upper layers are handled below. -/
theorem dualChild_exists_of_le_of_not_exception
    (i j : Fin 11) (hij : states i ≤ states j)
    (hexception : ¬ (i = 3 ∧ (j = 7 ∨ j = 9 ∨ j = 10))) :
    ∃ c : Fin 10,
      SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.child (orthogonalState j) c = orthogonalState i := by
  change (states i).toSubmodule ≤ (states j).toSubmodule at hij
  rw [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space, SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space] at hij
  have hchecked : ∀ a : Fin (charts i).1,
      (charts i).2.inclusion (Pi.single a 1) ∈ (charts j).2.space :=
    fun a ↦ hij ⟨Pi.single a 1, rfl⟩
  clear hij
  revert hchecked hexception
  fin_cases i <;> fin_cases j <;> decide +kernel +revert

/-- Every nonexceptional paired-eight state quotient has cyclic dual. -/
theorem nestedQuotient_dual_generated
    (i j : Fin 11) (hij : states i ≤ states j)
    (hexception : ¬ (i = 3 ∧ (j = 7 ∨ j = 9 ∨ j = 10))) :
    RepresentationGeneratedBy
      (nestedQuotientRepresentation (states i) (states j) hij).dual 1 := by
  obtain ⟨c, hc⟩ :=
    dualChild_exists_of_le_of_not_exception i j hij hexception
  let e : representation.Equiv representation.dual :=
    permutationFunctionRepresentationSelfDual (G := Top)
  let horth := selfDualOrthogonalSubrepresentation_antitone
    representation e hij
  have hstate : states (orthogonalState j) ≤
      states (orthogonalState i) := by
    rw [← orthogonalState_eq, ← orthogonalState_eq]
    exact horth
  have transport (A B A' B' : Subrepresentation representation)
      (hA : A = A') (hB : B = B') (hAB : A ≤ B) (hA'B' : A' ≤ B')
      (hgen : RepresentationGeneratedBy (nestedQuotientRepresentation A B hAB) 1) :
      RepresentationGeneratedBy (nestedQuotientRepresentation A' B' hA'B') 1 := by
    subst A'
    subst B'
    exact hgen
  have hchild : states (orthogonalState j) ≤
      states (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.registry.child (orthogonalState j) c) := by
    intro x hx
    change x ∈ (states (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.registry.child (orthogonalState j) c)).toSubmodule
    rw [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.registry.child_eq]
    exact Submodule.mem_sup_left hx
  have hchildGenerated : RepresentationGeneratedBy
      (nestedQuotientRepresentation (states (orthogonalState j))
        (states (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.registry.child (orthogonalState j) c)) hchild) 1 :=
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.registry.childQuotientRepresentation_generated (orthogonalState j) c
  have hgen : RepresentationGeneratedBy
      (nestedQuotientRepresentation
        (states (orthogonalState j))
        (states (orthogonalState i)) hstate) 1 :=
    transport _ _ _ _ rfl (congrArg states hc) hchild hstate hchildGenerated
  have hgenOrth : RepresentationGeneratedBy
      (nestedQuotientRepresentation
        (selfDualOrthogonalSubrepresentation representation e (states j))
        (selfDualOrthogonalSubrepresentation representation e (states i))
        horth) 1 :=
    transport _ _ _ _ (orthogonalState_eq j).symm
      (orthogonalState_eq i).symm hstate horth hgen
  let E := selfDualNestedQuotientEquiv representation e
    (states i) (states j) hij
  have htransport := representationGeneratedBy_of_surjective
    _ _ E.toIntertwiningMap E.surjective hgenOrth
  exact htransport

/-- A basis test produces the actual inclusion of two coordinate states. -/
private theorem states_le_of_basis (i j : Fin 11)
    (h : ∀ a : Fin (charts i).1,
      (charts i).2.inclusion (Pi.single a 1) ∈ (charts j).2.space) :
    states i ≤ states j := by
  change (states i).toSubmodule ≤ (states j).toSubmodule
  rw [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space, SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space]
  exact (charts i).2.le_of_basis_mem _ h

/-- The first exceptional quotient is a binary plane. -/
theorem exceptional_finrank_le_two
    (h37 : states (3 : Fin 11) ≤ states (7 : Fin 11)) :
    Module.finrank (ZMod 2)
      (nestedQuotientRepresentation (states 3) (states 7) h37).asModule ≤ 2 := by
  change Module.finrank (ZMod 2)
      ((states 7).toSubmodule ⧸
        (nestedSubrepresentation (states 3) (states 7) h37).toSubmodule) ≤ 2
  have hquot :=
    (nestedSubrepresentation (states 3) (states 7) h37).toSubmodule.finrank_quotient_add_finrank
  have hden := finrank_nestedSubrepresentation (states 3) (states 7) h37
  have hthree : Module.finrank (ZMod 2) (states 3).toSubmodule = 3 := by
    rw [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space, (charts 3).2.finrank]
    decide +kernel
  have hfive : Module.finrank (ZMod 2) (states 7).toSubmodule = 5 := by
    rw [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space, (charts 7).2.finrank]
    decide +kernel
  rw [hden, hthree, hfive] at hquot
  omega

/-- The checked displacement table supplies the fixed upper-layer test. -/
private theorem displacement_mem (j : Fin 11) (g : Top) (v : ModelModule)
    (hv : v ∈ states j) :
    representation g v - v ∈ states (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.displacementState j) := by
  have hmem : representation g v - v ∈
      (Representation.Coinvariants.ker (states j).toRepresentation).map
        (states j).toSubmodule.subtype := by
    exact ⟨(states j).toRepresentation g ⟨v, hv⟩ - ⟨v, hv⟩,
      Representation.Coinvariants.sub_mem_ker g (⟨v, hv⟩ : (states j).toSubmodule), rfl⟩
  rwa [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.coinvariantsKernel_map_eq_state] at hmem

/-- All three exceptions have finite derivations from the same certified
cyclic-dual quotient or a binary plane. -/
private theorem exceptional_certificate (j : Fin 11)
    (hj : j = 7 ∨ j = 9 ∨ j = 10) (h3j : states 3 ≤ states j) :
    BinaryNestedQuotientNonfixedCertificate representation (states 3) (states j) h3j := by
  have h38 : states 3 ≤ states 8 := states_le_of_basis 3 8 (by decide +kernel)
  have h89 : states 8 ≤ states 9 := states_le_of_basis 8 9 (by decide +kernel)
  have h910 : states 9 ≤ states 10 := states_le_of_basis 9 10 (by decide +kernel)
  have hbase : BinaryNestedQuotientNonfixedCertificate representation
      (states 3) (states 8) h38 :=
    .cyclic _ _ _ (nestedQuotient_dual_generated 3 8 h38 (by decide +kernel))
  have h9 : BinaryNestedQuotientNonfixedCertificate representation
      (states 3) (states 9) (h38.trans h89) :=
    .fixedExtension _ _ _ h38 h89 (displacement_mem 9) hbase
  rcases hj with rfl | rfl | rfl
  · exact .small _ _ _ (exceptional_finrank_le_two h3j)
  · exact h9
  · exact .fixedExtension _ _ _ (h38.trans h89) h910 (displacement_mem 10) h9

/-- Realization-free declaration: every nested pair has a finite
cyclic/small/fixed-extension certificate. -/
noncomputable def finiteGeneratorData :
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairTopNestedQuotientGeneratorData
        Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 where
  certificate := by
    intro A B hAB
    obtain ⟨i, rfl⟩ := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.registry.complete A
    obtain ⟨j, rfl⟩ := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.registry.complete B
    by_cases hexception : i = 3 ∧ (j = 7 ∨ j = 9 ∨ j = 10)
    · obtain ⟨rfl, hj⟩ := hexception
      exact exceptional_certificate j hj hAB
    · exact .cyclic _ _ _ (nestedQuotient_dual_generated i j hAB hexception)

/-- Uniform finite-state conclusion: every nonfixed simple row in every
nested paired-eight state quotient is bounded by one dual-generator layer,
namely its dimension over its Schur division ring. Ordinary cases use
the cyclic-dual certificate; the exceptions use a binary plane or certified
fixed upper layers. -/
theorem nestedQuotient_nonfixed_schurSocleMultiplicity_le_end_finrank
    (i j : Fin 11) (hij : states i ≤ states j)
    {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    (sigma : Representation (ZMod 2) Top A)
    (S : Submodule (ZMod 2)[Top] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[Top] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Top])
        (A := (nestedQuotientRepresentation
          (states i) (states j) hij).asModule) (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[Top] S) S := by
  exact finiteGeneratorData.subrepresentationQuotient_comp_nonfixed_le_end_finrank
    (MonoidHom.id Top) Function.surjective_id
    (states i) (states j) hij sigma S hnonfixed

/-- Catalogue-free semantic form of the finite theorem.  Completeness of
the eleven-state registry selects the two endpoints of an arbitrary nested
pair, after which the checked quotient table supplies the bound. -/
theorem subrepresentationQuotient_nonfixed_schurSocleMultiplicity_le_end_finrank
    (A B : Subrepresentation representation) (hAB : A ≤ B)
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (sigma : Representation (ZMod 2) Top X)
    (S : Submodule (ZMod 2)[Top] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[Top] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Top])
        (A := (nestedQuotientRepresentation A B hAB).asModule) (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[Top] S) S := by
  exact finiteGeneratorData.subrepresentationQuotient_comp_nonfixed_le_end_finrank
    (MonoidHom.id Top) Function.surjective_id A B hAB sigma S hnonfixed

/-- The semantic quotient bound survives pullback along any surjective group
map.  This is the form consumed by an original pair action: the finite state
quotient lives over the literal top, while its action on the actual quotient
group is obtained by inflation. -/
theorem subrepresentationQuotient_comp_nonfixed_le_end_finrank
    {H X : Type} [Group H]
    (gamma : H →* Top) (hgamma : Function.Surjective gamma)
    (A B : Subrepresentation representation) (hAB : A ≤ B)
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (sigma : Representation (ZMod 2) H X)
    (S : Submodule (ZMod 2)[H] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[H] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := (inflatedRepresentation gamma (nestedQuotientRepresentation A B hAB)).asModule)
        (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[H] S) S := by
  exact finiteGeneratorData.subrepresentationQuotient_comp_nonfixed_le_end_finrank
    gamma hgamma A B hAB sigma S hnonfixed

end PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators
end SymmetricSubgroupAsymptotics

end
