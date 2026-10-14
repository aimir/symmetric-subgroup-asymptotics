import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NormalStates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop1
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopStructuralAnchor

/-!
# Quotient socles and Schur data for paired-eight row 1

The shared row-0 normal-word registry has six states.  This file checks the
relative minimal-normal lattice and a uniformly padded two-position normal
generator for the socle above each state.  It transports those data to the
literal degree-eight top and combines them with the independently checked
natural-module generator theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightRow1QuotientSocles


abbrev Source := SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0TopCertificate.Source
local instance sourceGroup : Group Source := SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0TopCertificate.group

private def rowState (i : Fin 6) : Subgroup Source :=
  Subgroup.closure (Set.range (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0NormalCertificate.stateGenerators i))

private theorem rowState_injective : Function.Injective rowState :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NormalStates.state_injective

noncomputable def rowRegistry : FiniteNormalStateRegistry Source :=
  FiniteNormalStateRegistry.ofWordRegistry
    SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0NormalCertificate.topConjugacy.toCardinalCover SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0NormalCertificate.topAmbient
    SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0NormalCertificate.stateGenerators SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0NormalCertificate.data rowState_injective

noncomputable def topRegistry : FiniteNormalStateRegistry SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top :=
  rowRegistry.mapEquiv SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.actionEquiv

private abbrev RR := rowRegistry

private theorem rowRegistry_state (i : Fin 6) :
    RR.state i = rowState i := rfl

private def RowIsMinimalStateAbove (base j : Fin 6) : Prop :=
  rowState base < rowState j ∧
    ∀ k : Fin 6, rowState base < rowState k →
      rowState k ≤ rowState j → rowState k = rowState j

private abbrev MaskLE (i j : Fin 6) : Prop :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NormalStates.MaskLE i j

private theorem rowState_le_iff_maskLE (i j : Fin 6) :
    rowState i ≤ rowState j ↔ MaskLE i j :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NormalStates.state_le_iff_maskLE i j

private abbrev MaskMinimalStateAbove (base j : Fin 6) : Prop :=
  MaskLE base j ∧ ¬ MaskLE j base ∧
    ∀ k : Fin 6, (MaskLE base k ∧ ¬ MaskLE k base) →
      MaskLE k j → k = j

private theorem rowMinimal_iff_maskMinimal (base j : Fin 6) :
    RowIsMinimalStateAbove base j ↔ MaskMinimalStateAbove base j := by
  constructor
  · rintro ⟨hstrict, hminimal⟩
    refine ⟨(rowState_le_iff_maskLE base j).mp hstrict.1, ?_, ?_⟩
    · intro hback
      exact hstrict.2 ((rowState_le_iff_maskLE j base).mpr hback)
    · intro k hk hkj
      apply rowState_injective
      apply hminimal k
      · exact ⟨(rowState_le_iff_maskLE base k).mpr hk.1,
          fun h ↦ hk.2 ((rowState_le_iff_maskLE k base).mp h)⟩
      · exact (rowState_le_iff_maskLE k j).mpr hkj
  · rintro ⟨hforward, hback, hminimal⟩
    refine ⟨⟨(rowState_le_iff_maskLE base j).mpr hforward,
        fun h ↦ hback ((rowState_le_iff_maskLE j base).mp h)⟩, ?_⟩
    intro k hk hkj
    exact congrArg rowState (hminimal k
      ⟨(rowState_le_iff_maskLE base k).mp hk.1,
        fun h ↦ hk.2 ((rowState_le_iff_maskLE k base).mpr h)⟩
      ((rowState_le_iff_maskLE k j).mp hkj))

private theorem rowRegistry_minimal_iff (base j : Fin 6) :
    RR.IsMinimalStateAbove base j ↔ RowIsMinimalStateAbove base j := by
  rfl

private def carrierState (i : Fin 6) : Fin 6 :=
  ![3, 3, 5, 5, 5, 5] i

private theorem carrier_components_le : ∀ i : Fin 6,
    MaskLE i (carrierState i) ∧
      ∀ j : Fin 6, MaskMinimalStateAbove i j →
        MaskLE j (carrierState i) := by
  decide +kernel

private theorem carrier_le_of_components : ∀ i k : Fin 6,
    MaskLE i k →
      (∀ j : Fin 6, MaskMinimalStateAbove i j → MaskLE j k) →
        MaskLE (carrierState i) k := by
  decide +kernel

private def state0Generators : Fin 2 → Source := ![⟨4⟩, ⟨3⟩]
private def state1Generators : Fin 2 → Source := ![⟨2⟩, ⟨0⟩]
private def state2Generators : Fin 2 → Source := ![⟨12⟩, ⟨7⟩]
private def state3Generators : Fin 2 → Source := ![⟨7⟩, ⟨0⟩]
private def state4Generators : Fin 2 → Source := ![⟨4⟩, ⟨0⟩]
private def state5Generators : Fin 2 → Source := ![⟨0⟩, ⟨0⟩]

private def rowGenerator (i : Fin 6) : Fin 2 → Source :=
  ![state0Generators, state1Generators, state2Generators,
    state3Generators, state4Generators, state5Generators] i

private abbrev GeneratorIn (i k : Fin 6) : Prop :=
  ∀ j : Fin 2, SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NormalStates.normalMask k (rowGenerator i j).index = true

private theorem carrier_generator_facts : ∀ i : Fin 6,
    MaskLE i (carrierState i) ∧ GeneratorIn i (carrierState i) := by
  decide +kernel

private theorem carrier_le_of_generator : ∀ i k : Fin 6,
    MaskLE i k → GeneratorIn i k → MaskLE (carrierState i) k := by
  decide +kernel

private theorem row_carrier_eq_checked : ∀ i : Fin 6,
    rowState (carrierState i) = rowState i ⊔
      ⨆ j : {j : Fin 6 // RowIsMinimalStateAbove i j},
        rowState j.1 := by
  intro i
  let K : Subgroup Source := rowState i ⊔
    ⨆ j : {j : Fin 6 // RowIsMinimalStateAbove i j}, rowState j.1
  letI : (rowState i).Normal := RR.state_normal i
  letI (j : {j : Fin 6 // RowIsMinimalStateAbove i j}) :
      (rowState j.1).Normal := RR.state_normal j.1
  letI : (⨆ j : {j : Fin 6 // RowIsMinimalStateAbove i j},
      rowState j.1).Normal := ⟨by
    intro n hn g
    refine Subgroup.iSup_induction
      (fun j : {j : Fin 6 // RowIsMinimalStateAbove i j} ↦ rowState j.1)
      (C := fun x ↦ g * x * g⁻¹ ∈
        ⨆ j : {j : Fin 6 // RowIsMinimalStateAbove i j}, rowState j.1)
      hn ?_ ?_ ?_
    · intro j x hx
      exact Subgroup.mem_iSup_of_mem j
        ((show (rowState j.1).Normal from inferInstance).conj_mem x hx g)
    · simp
    · intro x y hx hy
      simpa [mul_assoc] using mul_mem hx hy⟩
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  obtain ⟨k, hk⟩ := RR.complete K
  have hk' : rowState k = K := (rowRegistry_state k).symm.trans hk
  change rowState (carrierState i) = K
  apply le_antisymm
  · rw [← hk']
    apply (rowState_le_iff_maskLE (carrierState i) k).mpr
    apply carrier_le_of_components i k
    · apply (rowState_le_iff_maskLE i k).mp
      rw [hk']
      exact le_sup_left
    · intro j hj
      apply (rowState_le_iff_maskLE j k).mp
      rw [hk']
      exact le_sup_of_le_right (le_iSup
        (fun z : {z : Fin 6 // RowIsMinimalStateAbove i z} ↦ rowState z.1)
        ⟨j, (rowMinimal_iff_maskMinimal i j).mpr hj⟩)
  · dsimp [K]
    apply sup_le
    · exact (rowState_le_iff_maskLE i (carrierState i)).mpr
        (carrier_components_le i).1
    · apply iSup_le
      rintro ⟨j, hj⟩
      exact (rowState_le_iff_maskLE j (carrierState i)).mpr
        ((carrier_components_le i).2 j
          ((rowMinimal_iff_maskMinimal i j).mp hj))

private theorem row_generated_checked : ∀ i : Fin 6,
    Subgroup.normalClosure (Set.range (rowGenerator i)) ⊔ rowState i =
      rowState (carrierState i) := by
  intro i
  let L : Subgroup Source :=
    Subgroup.normalClosure (Set.range (rowGenerator i)) ⊔ rowState i
  letI : (rowState i).Normal := RR.state_normal i
  letI : L.Normal := by
    dsimp [L]
    infer_instance
  obtain ⟨k, hk⟩ := RR.complete L
  have hk' : rowState k = L := (rowRegistry_state k).symm.trans hk
  change L = rowState (carrierState i)
  apply le_antisymm
  · dsimp [L]
    apply sup_le
    · letI : (rowState (carrierState i)).Normal :=
        RR.state_normal (carrierState i)
      apply Subgroup.normalClosure_le_normal
      rintro x ⟨j, rfl⟩
      apply (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NormalStates.normalMask_mem
        (carrierState i) (rowGenerator i j)).mp
      exact (carrier_generator_facts i).2 j
    · exact (rowState_le_iff_maskLE i (carrierState i)).mpr
        (carrier_generator_facts i).1
  · rw [← hk']
    apply (rowState_le_iff_maskLE (carrierState i) k).mpr
    apply carrier_le_of_generator i k
    · apply (rowState_le_iff_maskLE i k).mp
      rw [hk']
      exact le_sup_right
    · intro j
      have hmemL : rowGenerator i j ∈ L :=
        Subgroup.mem_sup_left
          (Subgroup.subset_normalClosure (Set.mem_range_self j))
      have hmemk : rowGenerator i j ∈ rowState k := by
        rw [hk']
        exact hmemL
      exact (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NormalStates.normalMask_mem k (rowGenerator i j)).mpr hmemk

noncomputable def rowStateData (i : Fin 6) :
    FiniteRelativeSocleGeneratorData Source (RR.state i) 2 :=
  RR.relativeSocleGeneratorDataOfStates i (carrierState i) 2
    {j : Fin 6 // RowIsMinimalStateAbove i j}
    Subtype.val
    (fun j ↦ (rowRegistry_minimal_iff i j).2 j.property)
    (fun j hj ↦ ⟨⟨j, (rowRegistry_minimal_iff i j).1 hj⟩, rfl⟩)
    (by simpa only [rowRegistry_state] using row_carrier_eq_checked i)
    (rowGenerator i)
    (by simpa only [rowRegistry_state] using row_generated_checked i)

noncomputable def topStateData (i : Fin 6) :
    FiniteRelativeSocleGeneratorData SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top (topRegistry.state i) 2 :=
  (rowStateData i).mapEquiv SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.actionEquiv

/-- The shared literal-top normal registry, indexed however it chooses,
inherits the checked two-position quotient-socle family from the six-state
source registry by semantic completeness. -/
noncomputable def family :
    (SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1.normalRegistry).QuotientSocleGeneratorFamily 2 where
  data := by
    intro i
    let N := SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1.normalRegistry.state i
    letI : N.Normal := SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1.normalRegistry.state_normal i
    let j := (topRegistry.complete N).choose
    have hj : topRegistry.state j = N := (topRegistry.complete N).choose_spec
    exact cast
      (congrArg
        (fun M : Subgroup SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top ↦
          FiniteRelativeSocleGeneratorData SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top M 2) hj)
      (topStateData j)

/-- Concrete row-1 Schur data.  The realization is arbitrary because both
finite inputs depend only on the literal top selected by the catalogue. -/
noncomputable def schurData
    {p : PreE7PairActionClass 8}
    {R : DegreeTwoPairTopRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p} :
    DegreeTwoPairTopSchurData SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p R :=
  DegreeTwoPairTopSchurData.ofUniform 2 2 family (by
    change UniformSubrepresentationGeneratorBound SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.representation 2
    exact SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.uniform)

end DegreeTwoPairedEightRow1QuotientSocles
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
