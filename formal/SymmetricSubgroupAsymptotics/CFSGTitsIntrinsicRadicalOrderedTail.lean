import SymmetricSubgroupAsymptotics.CFSGOpposedPeelingFirstTrivialParameters
import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFirstLayer
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveOrderedParameters
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleGenerators

/-! The SAME actual strict intersection has a seven-block ordered tail
cover: its first middle inversion coordinate is exactly one. At the
binary parameter the first bounded exponent is therefore zero. The
original derived membership is retained on the WHOLE product; no
individual remaining block is asserted to lie in the derived group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicRadicalOrderedTail
open CFSGOpposedPeelingFirstTrivialParameters CFSGOpposedPeelingOrderedParameters
open CFSGOpposedSubgroupPeeling CFSGOpposedSubgroupPeelingChain
open CFSGReeFFourMiddlePositiveIntersectionNormalizer
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourInversionPeelingWords CFSGReeFFourInversionPeeling
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedSubgroupPeeling
open CFSGReeFFourBinaryPositiveOrderedParameters CFSGReeFFourBinaryMiddleGenerators
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourOuterThreeWord
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourMinimalParabolics
open CFSGTitsIntrinsicMiddleRadical CFSGTitsIntrinsicFirstLayer

private theorem first_step (m : ℕ) : step m true 0=middleFixedWeyl m := by
  change simpleWeyl m true=middleFixedWeyl m
  exact simpleWeyl_true m

private theorem first_at_zero {G : Type*} [One G] (b : Fin 8→G)
    (h : ∀h : 0<8,b ⟨0,h⟩=1) : b 0=1 := h (by decide)

theorem middle_intersection_ordered_cover (m : ℕ) (u : originalModelFixed m)
    (hu : u∈middlePositiveIntersection m) :
    ∃b : Fin 8 → originalModelFixed m,
      (∀j,b j∈inversionPart (fixedPositive m) (fixedNegative m) (step m true j.val)) ∧
      u=orderedProduct (step m true) 8 b ∧ b 0=1 := by
  have hc : step m true 0*u*(step m true 0)⁻¹∈fixedPositive m := by
    rw [first_step]
    exact hu.2
  obtain ⟨b,hb,he,hfirst⟩ := exists_parameters_first_one_of_opposition
    (fixedPositive m) (fixedNegative m) (step m true) 8
    (fixed_positive_negative_disjoint m)
    (fun j hj => simple_block_le_residual m true ⟨j,hj⟩)
    (fun j _ => fixed_sign_factorization m [axis true j])
    (by rw [eighth_prefix_eq_opposition]; exact (fixed_positive_image_eq_fixed_negative m).le)
    u hu.1 hc
  exact ⟨b,hb,he,first_at_zero b hfirst⟩

private theorem bounded_power {G : Type*} [Group G] [Finite G]
    (g x : G) (n : ℕ) (hn : 0<n) (hg : g^n=1) (hx : x∈Subgroup.zpowers g) :
    ∃i : Fin n,g^i.val=x := by
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hx)
  have hkn : k<n := (Finset.mem_range.mp hk).trans_le
    (Nat.le_of_dvd hn (orderOf_dvd_of_pow_eq_one hg))
  exact ⟨⟨k,hkn⟩,he⟩

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (CFSGReeFFourFixedAmbientHom.fixedAmbientHom m)
    (CFSGReeFFourFixedAmbientHom.fixedAmbientHom_injective m)

theorem binary_middle_intersection_power_cover (u : originalModelFixed 0)
    (hu : u∈middlePositiveIntersection 0) :
    ∃a : ∀j : Fin 8,Fin (blockPeriod j),
      u=orderedProduct (step 0 true) 8 (fun j => (blockBase j)^(a j).val) ∧
      (a 0).val=0 := by
  obtain ⟨b,hb,he,hfirst⟩ := middle_intersection_ordered_cover 0 u hu
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
    apply bounded_power (blockBase j) (b j) (blockPeriod j) hpos hperiod
    rw [←binary_step_block_eq]
    exact hb j
  choose a ha using hp
  have hpow : (fourCycle 0)^(a 0).val=1 := (ha 0).trans hfirst
  have hd : 4∣(a 0).val := by
    simpa only [fourCycle_order_four] using orderOf_dvd_of_pow_eq_one hpow
  have hz : (a 0).val=0 := Nat.eq_zero_of_dvd_of_lt hd (a 0).isLt
  refine ⟨a,he.trans ?_,hz⟩
  apply congrArg (orderedProduct (step 0 true) 8)
  funext j
  exact (ha j).symm

theorem radical_source_power_cover (x : middleRadical) :
    ∃a : ∀j : Fin 8,Fin (blockPeriod j),
      (((sourceEquiv.symm x).val : commutator (originalModelFixed 0)) : originalModelFixed 0)=
        orderedProduct (step 0 true) 8 (fun j => (blockBase j)^(a j).val) ∧
      (a 0).val=0 :=
  binary_middle_intersection_power_cover _ (sourceEquiv.symm x).property

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicRadicalOrderedTail
