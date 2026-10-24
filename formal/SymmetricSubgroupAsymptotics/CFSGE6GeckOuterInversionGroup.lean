import SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTripleChart
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterInversionRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine

/-! The actual inversion subgroup of the outer paired E6 word is the
range of the three-parameter orthogonal chart. The support recognition
and the genuine root-line equality retain arbitrary selected-root signs.
No diagram or Ree fixed-point lift is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOuterInversionGroup
open CFSGE6GeckOuterTripleChart CFSGE6GeckOrthogonalPairChart CFSGE6GeckSignedSimpleParameters
open CFSGReeFFourOuterInversionRoots CFSGExceptionalNormTwoBases
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateWeylIntersectionFactor
open CFSGNormTwoCoordinateWeylIntersectionCardinality CFSGNormTwoCoordinateNegativeRootContainment
open CFSGNormTwoCoordinateRootWeylAction
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

def outerInversion (K : Type) [Field K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  Positive K ⊓ (Negative K).comap
    (MulAut.conj (canonicalWord rawData K blockWord)).toMonoidHom

private theorem simpleLine_le_triple (K : Type) [Field K] (i : Fin 6) (hi : i∈blockNodes) :
    canonicalRootSubgroup rawData K false i≤(rawTripleHom K).range := by
  rw [rawTripleHom_range,rawPairHom_range]
  simp only [blockNodes,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl
  · intro x hx
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)
  · rintro _ ⟨a,rfl⟩
    exact Subgroup.mem_sup_right ⟨Multiplicative.ofAdd a,rfl⟩
  · intro x hx
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)

private theorem simpleLine_le_inversion (K : Type) [Field K]
    (i : Fin 6) (hi : i∈blockNodes) :
    canonicalRootSubgroup rawData K false i≤outerInversion K := by
  rintro _ ⟨a,rfl⟩
  refine ⟨(CFSGNormTwoCoordinateLeadingHom.positiveRoot A hd hs hp ho K i a).property,?_⟩
  have hline : rootSubgroup A hd hs hp ho K (coordinateRoot A hd i)=
      canonicalRootSubgroup rawData K false i :=
    rootSubgroup_simple_eq_canonical A hd hs hp ho K i
  have hr : canonicalRoot rawData K false i a∈
      rootSubgroup A hd hs hp ho K (coordinateRoot A hd i) := hline.symm ▸ ⟨a,rfl⟩
  have hn : ∀j,(CFSGNormTwoGeckWeylWordDegree.wordRoot A hs hp
      (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho)
      blockWord (coordinateRoot A hd i)).val j≤0 := by
    rw [outer_word_simple_val i hi]
    intro j
    simp only [Pi.neg_apply]
    apply neg_nonpos.mpr
    simp only [Pi.single_apply]
    split_ifs <;> omega
  apply negative_root_subgroup_le A hd hs hp ho K _ hn
  rw [←rootSubgroup_map_word A hd hs hp ho K blockWord (coordinateRoot A hd i)]
  exact ⟨canonicalRoot rawData K false i a,hr,rfl⟩

theorem outerInversion_eq_triple_range (K : Type) [Field K] [Finite K] :
    outerInversion K=(rawTripleHom K).range := by
  apply le_antisymm
  · intro x hx
    let u : PositiveGroup A hd hs hp ho K := ⟨x,hx.1⟩
    have hu : u∈wordSignPart A hd hs hp ho K blockWord true := hx.2
    rw [←signRootGroup_eq_part A hd hs hp ho K blockWord true] at hu
    have hle : signRootGroup A hd hs hp ho K blockWord true≤
        ((rawTripleHom K).range).comap (PositiveGroup A hd hs hp ho K).subtype := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨k,a,rfl⟩
      have hk : ¬∀j,0≤(CFSGNormTwoGeckWeylWordDegree.wordRoot A hs hp
          (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho)
          blockWord k.val.val).val j := by
        simpa only [signRoots,if_true,Finset.mem_filter,Finset.mem_univ,true_and] using k.property
      obtain ⟨i,hi,he⟩ := (outer_negative_iff k.val).mp hk
      change selectedRootElement A hd hs hp ho K k.val.val a.toAdd∈(rawTripleHom K).range
      have hr := selectedRootElement_mem A hd hs hp ho K k.val.val a.toAdd
      rw [he] at hr ⊢
      have hline : rootSubgroup A hd hs hp ho K (coordinateRoot A hd i)=
          canonicalRootSubgroup rawData K false i :=
        rootSubgroup_simple_eq_canonical A hd hs hp ho K i
      rw [hline] at hr
      exact simpleLine_le_triple K i hi hr
    exact hle hu
  · rw [rawTripleHom_range,rawPairHom_range]
    apply sup_le
    · exact sup_le (simpleLine_le_inversion K 0 (by decide))
        (simpleLine_le_inversion K 5 (by decide))
    · rintro _ ⟨a,rfl⟩
      exact simpleLine_le_inversion K 1 (by decide) ⟨a.toAdd,rfl⟩

theorem exists_triple_of_inversion (K : Type) [Field K] [Finite K]
    (x : (Matrix GeckIndex GeckIndex K)ˣ) (hx : x∈outerInversion K) :
    ∃a : (Multiplicative K×Multiplicative K)×Multiplicative K,rawTripleHom K a=x := by
  rw [outerInversion_eq_triple_range] at hx
  exact hx

end SymmetricSubgroupAsymptotics.CFSGE6GeckOuterInversionGroup
