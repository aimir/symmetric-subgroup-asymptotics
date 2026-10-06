import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourTraceyCapacity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveCharacterIntervalSource

/-!
# Tracey bound for the degree-four translation-carried normal section

This narrow consumer applies the generic prime-explicit Tracey transport to
one concrete normal subrepresentation of the actual correlated translation
module.  Its exported statement mentions only the normal-generator bound;
the dependent induced representation is confined to the proof body.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private theorem degreeFour_half_le_socleSlots (s : ℕ) (hs : 2 ≤ s) :
    s / 2 ≤ degreeFourSocleSlots s := by
  by_cases hsmall : s = 2 ∨ s = 3
  · rcases hsmall with rfl | rfl <;> norm_num [degreeFourSocleSlots]
  · simp only [degreeFourSocleSlots, if_neg hsmall]
    omega

private noncomputable def degreeFourTraceyLiteralLocalRepresentation
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (i : block.Points) :
    Representation (ZMod (localTranslationChart block P).p)
      (MulAction.stabilizer (preE7NonPairAction w U) i)
      (localTranslationChart block P).V :=
  ActualWreathAffineCapacity.localRepresentation
    (initialState hTraceyPerm block) (localMap block P)
    (localTranslationChart block P) i

private abbrev DegreeFourTraceyTranslationModule
    (hTraceyPerm : TraceyPermutationGeneratorInput) :=
  PermutationalWreathProduct.Compression.ElementarySubmodule
    (p := (localTranslationChart block P).p)
    (initialState hTraceyPerm block).rho (localMap block P)
    (localTranslationChart block P).equiv.symm

private noncomputable def degreeFourTraceyLiteralAmbientRepresentation
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    Representation (ZMod (localTranslationChart block P).p)
      (preE7NonPairAction w U)
      (DegreeFourTraceyTranslationModule block P hTraceyPerm) :=
  ActualWreathAffineCapacity.ambientRepresentation
    (initialState hTraceyPerm block) (localMap block P)
    (localTranslationChart block P)

private noncomputable def degreeFourTraceyLiteralInducedRepresentation
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (i : block.Points) :
    Representation (ZMod (localTranslationChart block P).p)
      (preE7NonPairAction w U)
      (Representation.IndV
        (MulAction.stabilizer (preE7NonPairAction w U) i).subtype
        (degreeFourTraceyLiteralLocalRepresentation block P hTraceyPerm i)) :=
  Representation.ind
    (MulAction.stabilizer (preE7NonPairAction w U) i).subtype
    (degreeFourTraceyLiteralLocalRepresentation block P hTraceyPerm i)

private noncomputable def degreeFourTraceyLiteralIntertwiner
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (i : block.Points) :
    Representation.IntertwiningMap
      (degreeFourTraceyLiteralAmbientRepresentation block P hTraceyPerm)
      (degreeFourTraceyLiteralInducedRepresentation
        block P hTraceyPerm i) :=
  ActualWreathAffineCapacity.inducedIntertwiner
    (initialState hTraceyPerm block) (localMap block P)
    (localTranslationChart block P) i

private theorem degreeFourTraceyLiteralIntertwiner_injective
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (i : block.Points) :
    Function.Injective
      (degreeFourTraceyLiteralIntertwiner block P hTraceyPerm i) :=
  ActualWreathAffineCapacity.inducedIntertwiner_injective
    (initialState hTraceyPerm block) (localMap block P)
    (localTranslationChart block P) i

private theorem degreeFourTraceyLiteralInduced_uniform_half
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (i : block.Points) :
    UniformSubrepresentationGeneratorBound
      (degreeFourTraceyLiteralInducedRepresentation
        block P hTraceyPerm i)
      (Nat.card block.Points / 2) := by
  letI : Fintype block.Points := Fintype.ofFinite _
  let C := localTranslationChart block P
  let rho := degreeFourTraceyLiteralLocalRepresentation
    block P hTraceyPerm i
  let NTracey : Subgroup (preE7NonPairAction w U) :=
    degreeFourTraceySubgroup block P hTraceyPerm hs
  letI : IsSolvable NTracey :=
    degreeFourTraceySubgroup_isSolvable block P hTraceyPerm hr hs
  obtain ⟨P₂, hP₂, hHall⟩ :=
    exists_degreeFourTraceyTwoComplement block P hTraceyPerm hr hs
  have hp : C.p = 2 := by
    simpa only [C, localTranslationChart] using
      degreeFour_profilePrime_eq_two block P hr
  have hdim : Module.finrank (ZMod C.p) C.V = 2 := by
    let C0 := chart block P
    letI : Finite C0.V := Finite.of_injective
      (fun v : C0.V ↦ C0.equiv.symm (Multiplicative.ofAdd v))
      C0.equiv.symm.injective
    have hdegree : 4 = P.p ^ C0.d := by
      rw [← hr]
      simpa [PrimitiveAffineProfile.ElementaryChart.d] using
        P.degree_eq_prime_pow_finrank C0.equiv (origin block)
    have hd0 : C0.d = 2 :=
      (prime_pow_positive_injective (d := C0.d) (e := 2)
        P.p_prime Nat.prime_two C0.d_pos (by norm_num)
        (hdegree.symm.trans (by norm_num))).2
    simpa only [C, C0, localTranslationChart,
      PrimitiveAffineProfile.ElementaryChart.d] using hd0
  have hchi : primeTraceyLocalDualOrbitCount i rho NTracey P₂ = 1 :=
    degreeFourTraceyLocalDualOrbitCount_eq_one
      block P hTraceyPerm hr hs hD P₂ hP₂ hHall i
  have horbit :
      ∀ e : MulAction.orbitRel.Quotient NTracey block.Points → ℕ,
        (∀ o, TraceyBinarySolubleFormulaBounds
          (Nat.card o.orbit) (e o)) →
        (∑ o, e o) ≤ Nat.card block.Points / 2 := by
    intro e he
    have h := degreeFourTracey_esol_sum_le_half
      block P hTraceyPerm hs e he
    dsimp only [NTracey] at h ⊢
    convert h using 1
    apply Finset.sum_congr
    · ext o
      simp
    · intro o ho
      rfl
  have hTraceyP : PrimeTraceySolubleOrbitInducedModuleInput C.p :=
    primeTraceySolubleOrbitInducedModuleInput_of_eq_two hTracey hp
  change UniformSubrepresentationGeneratorBound
    (Representation.ind
      (MulAction.stabilizer (preE7NonPairAction w U) i).subtype rho)
    (Nat.card block.Points / 2)
  exact hTraceyP.uniform_half i rho NTracey P₂ hP₂ hchi hdim horbit

/- Every translation-carried retained normal subgroup, and hence the
translation-selected socle part, inherits the sharp slot budget. -/
theorem degreeFourTranslationCarried_normalGen_le_sharp
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (i0 : block.Points)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (DegreeFourRetainedQuotient N)) [H.Normal]
    (hH : H ≤ degreeFourTranslationImage block P N) :
    MarkedC4.normalGen H ≤
      degreeFourSocleSlots (Nat.card block.Points) := by
  let L := degreeFiveTranslationPreimage block P N H
  have hLgen : MarkedC4.normalGen L ≤
      degreeFourSocleSlots (Nat.card block.Points) := by
    apply normalGen_le_of_elementaryNormalSubrepresentation_comp_generated
      (E block P) (elementaryChart block P) L
      (degreeFiveTranslationPreimage_le_translation block P N H)
    let sigma := degreeFourTraceyLiteralAmbientRepresentation
      block P hTraceyPerm
    let f := degreeFourTraceyLiteralIntertwiner
      block P hTraceyPerm i0
    let M0 := (elementaryChart block P).originalKernelChart
      |>.normalSubrepresentation (QuotientGroup.mk' (E block P))
        (QuotientGroup.mk'_surjective (E block P))
        (elementaryChart block P).quotientRepresentation L
    let M : Subrepresentation sigma :=
      ActualWreathAffineCapacity.subrepresentationComp
        (QuotientGroup.mk' (E block P))
        (elementaryChart block P).quotientRepresentation.ρ M0
    have hinduced : UniformSubrepresentationGeneratorBound
        (degreeFourTraceyLiteralInducedRepresentation
          block P hTraceyPerm i0)
        (Nat.card block.Points / 2) := by
      exact degreeFourTraceyLiteralInduced_uniform_half
        block P hTracey hTraceyPerm hr hs hD i0
    have htransport : UniformSubrepresentationGeneratorBound sigma
        (Nat.card block.Points / 2) :=
      hinduced.of_injective f
        (degreeFourTraceyLiteralIntertwiner_injective
          block P hTraceyPerm i0)
    have hMhalf : RepresentationGeneratedBy M.toRepresentation
        (Nat.card block.Points / 2) :=
      htransport M
    have hM := representationGeneratedBy_mono M.toRepresentation
      (degreeFour_half_le_socleSlots (Nat.card block.Points) hs)
      hMhalf
    simpa only [ActualWreathAffineCapacity.ambientRepresentation,
      initialState, localTranslationChart, elementaryChart,
      ActualWreathAffineCapacity.E,
      PermutationalWreathProduct.Compression.kernelElementaryChart,
      M, M0, sigma, degreeFourTraceyLiteralAmbientRepresentation,
      DegreeFourTraceyTranslationModule] using hM
  rw [← degreeFiveTranslationPreimage_map_eq block P N H hH]
  exact (MarkedC4.normalGen_map_le (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1) L).trans hLgen


end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
