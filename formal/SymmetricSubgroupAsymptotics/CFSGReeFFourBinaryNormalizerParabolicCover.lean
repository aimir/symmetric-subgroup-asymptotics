import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryNormalizerShortWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleGenerators
import SymmetricSubgroupAsymptotics.CFSGReeFFourMinimalParabolics

/-! The actual binary Bruhat cover and the proved short-word exclusion
put the normalizer of the SAME large positive subgroup in one of the
two literal minimal parabolics. Subgroup-union containment chooses the
parabolic; no whole-group simplicity or generation assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryNormalizerParabolicCover
open CFSGReeFFourBinaryNormalizerShortWords CFSGReeFFourBinaryMiddleGenerators
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourShortPairedWeylMenu CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourMinimalParabolics
open CFSGReeFFourOuterParabolicFlag CFSGReeFFourMiddleParabolicFlag

private theorem small_word_mem (i : Fin 16) (hi : i.val ≤ 2) :
    shortModelWord 0 i ∈ simpleParabolic 0 false ∨
      shortModelWord 0 i ∈ simpleParabolic 0 true := by
  have hindex : i = (0 : Fin 16) ∨ i = (1 : Fin 16) ∨ i = (2 : Fin 16) := by
    have hn : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hn with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  have hw (b : Bool) : simpleWeyl 0 b ∈ simpleParabolic 0 b :=
    (show Subgroup.closure {simpleWeyl 0 b} ≤ simpleParabolic 0 b from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _))
  rcases hindex with rfl | rfl | rfl
  · left
    change (1 : originalModelFixed 0) ∈ simpleParabolic 0 false
    exact (simpleParabolic 0 false).one_mem
  · exact Or.inl (hw false)
  · exact Or.inr (hw true)

theorem normalizer_mem_one_simpleParabolic
    (S : Subgroup (originalModelFixed 0)) (hS : S ≤ fixedPositive 0)
    (hcard : 512 ≤ Nat.card S)
    (hU : fixedPositive 0 ≤ Subgroup.normalizer (S : Set (originalModelFixed 0)))
    (g : originalModelFixed 0)
    (hg : g ∈ Subgroup.normalizer (S : Set (originalModelFixed 0))) :
    g ∈ simpleParabolic 0 false ∨ g ∈ simpleParabolic 0 true := by
  let N := Subgroup.normalizer (S : Set (originalModelFixed 0))
  obtain ⟨u, d, i, v, he⟩ := exists_short_fixed_cell 0 g
  have hd : d.val = 1 := by
    have hb : d.val ∈ (⊥ : Subgroup (originalModelFixed 0)) :=
      (le_of_eq fixedDiagonal_zero_eq_bot) d.property
    exact Subgroup.mem_bot.mp hb
  have he' : g = u.val * shortModelWord 0 i * v.val := by
    simpa only [hd, mul_one] using he
  have hw : shortModelWord 0 i ∈ N := by
    have hc : u.val⁻¹ * g * v.val⁻¹ = shortModelWord 0 i := by
      rw [he']
      group
    exact hc ▸ N.mul_mem (N.mul_mem (N.inv_mem (hU u.property)) hg)
      (N.inv_mem (hU v.property))
  have hi := normalizing_shortModelWord_index_le_two S hS hcard i hw
  have hpos (b : Bool) : fixedPositive 0 ≤ simpleParabolic 0 b :=
    (positive_le_borel 0).trans le_sup_left
  rcases small_word_mem i hi with hb | hb
  · left
    rw [he']
    exact (simpleParabolic 0 false).mul_mem
      ((simpleParabolic 0 false).mul_mem (hpos false u.property) hb) (hpos false v.property)
  · right
    rw [he']
    exact (simpleParabolic 0 true).mul_mem
      ((simpleParabolic 0 true).mul_mem (hpos true u.property) hb) (hpos true v.property)

theorem normalizer_le_some_simpleParabolic
    (S : Subgroup (originalModelFixed 0)) (hS : S ≤ fixedPositive 0)
    (hcard : 512 ≤ Nat.card S)
    (hU : fixedPositive 0 ≤ Subgroup.normalizer (S : Set (originalModelFixed 0))) :
    ∃ b : Bool, Subgroup.normalizer (S : Set (originalModelFixed 0)) ≤ simpleParabolic 0 b := by
  have hcover : (Subgroup.normalizer (S : Set (originalModelFixed 0)) : Set (originalModelFixed 0)) ⊆
      (simpleParabolic 0 false : Set (originalModelFixed 0)) ∪ simpleParabolic 0 true := by
    intro g hg
    exact normalizer_mem_one_simpleParabolic S hS hcard hU g hg
  rcases SubgroupClass.subset_union.mp hcover with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

theorem normalizer_le_outer_or_middle
    (S : Subgroup (originalModelFixed 0)) (hS : S ≤ fixedPositive 0)
    (hcard : 512 ≤ Nat.card S)
    (hU : fixedPositive 0 ≤ Subgroup.normalizer (S : Set (originalModelFixed 0))) :
    Subgroup.normalizer (S : Set (originalModelFixed 0)) ≤ outerParabolic 0 ∨
      Subgroup.normalizer (S : Set (originalModelFixed 0)) ≤ middleParabolic 0 := by
  obtain ⟨b, hb⟩ := normalizer_le_some_simpleParabolic S hS hcard hU
  cases b
  · exact Or.inl ((simpleParabolic_false 0) ▸ hb)
  · exact Or.inr ((simpleParabolic_true 0) ▸ hb)

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryNormalizerParabolicCover
