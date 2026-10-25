import SymmetricSubgroupAsymptotics.CFSGOpposedPeelingOrderedParameters
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryAbelianGenerators

/-! Eight literal opposed peels cover the actual fixed positive group.
At m=0 the genuine inversion blocks are the two/four-power blocks,
so the resulting domain has four binary and four two-bit parameters.
No BFS enumeration, group-order inference, or centre assertion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveOrderedParameters
open CFSGOpposedPeelingOrderedParameters CFSGOpposedSubgroupPeeling
open CFSGOpposedSubgroupPeelingChain CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourInversionPeelingWords
open CFSGReeFFourInversionPeeling CFSGReeFFourFixedSubgroupPeeling
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourBinaryAbelianGenerators
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourOuterThreeWord
open CFSGReeFFourFixedAmbientHom

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem positive_ordered_cover (m : ℕ) (u : originalModelFixed m)
    (hu : u∈fixedPositive m) :
    ∃b : Fin 8 → originalModelFixed m,
      (∀j,b j∈inversionPart (fixedPositive m) (fixedNegative m) (step m true j.val)) ∧
      u=orderedProduct (step m true) 8 b := by
  apply exists_parameters_of_opposition (fixedPositive m) (fixedNegative m)
    (step m true) 8 (fixed_positive_negative_disjoint m)
      (fun j hj => simple_block_le_residual m true ⟨j,hj⟩)
      (fun j _ => fixed_sign_factorization m [axis true j]) ?_ u hu
  rw [eighth_prefix_eq_opposition]
  exact (fixed_positive_image_eq_fixed_negative m).le

def blockBase (j : Fin 8) : originalModelFixed 0 :=
  if axis true j.val then fourCycle 0 else outerInvolution 0

def blockPeriod (j : Fin 8) : ℕ := if axis true j.val then 4 else 2

theorem binary_step_block_eq (j : Fin 8) :
    inversionPart (fixedPositive 0) (fixedNegative 0) (step 0 true j.val)=
      Subgroup.zpowers (blockBase j) := by
  change CFSGReeFFourAbelianImageCardinality.positiveBlock 0 (axis true j.val)=
    Subgroup.zpowers (if axis true j.val then fourCycle 0 else outerInvolution 0)
  cases h : axis true j.val
  · exact positiveBlock_false_eq_zpowers
  · exact positiveBlock_true_eq_zpowers

private theorem exists_bounded_power {G : Type*} [Group G] [Finite G]
    (g x : G) (n : ℕ) (hn : 0<n) (hg : g^n=1) (hx : x∈Subgroup.zpowers g) :
    ∃i : Fin n,g^i.val=x := by
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hx)
  have hkn : k<n := (Finset.mem_range.mp hk).trans_le
    (Nat.le_of_dvd hn (orderOf_dvd_of_pow_eq_one hg))
  exact ⟨⟨k,hkn⟩,he⟩

theorem binary_power_cover (u : originalModelFixed 0) (hu : u∈fixedPositive 0) :
    ∃a : ∀j : Fin 8,Fin (blockPeriod j),
      u=orderedProduct (step 0 true) 8 (fun j => (blockBase j)^(a j).val) := by
  obtain ⟨b,hb,he⟩ := positive_ordered_cover 0 u hu
  have hp : ∀j : Fin 8,∃i : Fin (blockPeriod j),(blockBase j)^i.val=b j := by
    intro j
    have hpos : 0<blockPeriod j := by
      unfold blockPeriod
      cases axis true j.val <;> decide
    have hperiod : (blockBase j)^(blockPeriod j)=1 := by
      unfold blockBase blockPeriod
      cases axis true j.val
      · exact outerInvolution_square 0
      · exact fourCycle_four 0
    apply exists_bounded_power (blockBase j) (b j) (blockPeriod j) hpos hperiod
    rw [←binary_step_block_eq]
    exact hb j
  choose a ha using hp
  refine ⟨a,he.trans ?_⟩
  apply congrArg (orderedProduct (step 0 true) 8)
  funext j
  exact (ha j).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveOrderedParameters
