import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedNormalizerParabolic
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicCardinality

/-! The checked 2048-element positive/derived intersection has exactly the
full positive subgroup as normalizer in the ORIGINAL full fixed group.
Only the existing Bruhat cover, exact intersection count and literal
outer three-word identity are used. No self-normalizing-Borel or BN-pair
recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryExactPositiveNormalizer
open CFSGReeFFourBinaryDerivedNormalizerParabolic CFSGReeFFourBinaryOuterSaving
open CFSGReeFFourBinaryNormalizerShortWords CFSGReeFFourReducedPositiveIntersection
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedAmbientHom CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourFixedPositiveCardinality CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourOuterThreeWord
open CFSGReeFFourOuterParabolicCardinality CFSGReeFFourFixedBruhatCover

private abbrev P := ambientDerivedPositive 0
private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

private theorem positive_card_lower : 2048 ≤ Nat.card P :=
  derivedPositive_card_ge_2048.trans_eq
    (Nat.card_congr (derivedPositiveEquivAmbient 0).toEquiv)

private theorem not_normalizer_of_three_word {G : Type*} [Group G]
    (S U : Subgroup G) (hSU : S≤U) (x w : G) (hx : x∈S)
    (hw : w=x*(w*x*w⁻¹)*x) (hwU : w∉U) :
    w∉Subgroup.normalizer (S : Set G) := by
  intro hn
  have hc : w*x*w⁻¹∈S := (hn x).mp hx
  apply hwU
  rw [hw]
  exact U.mul_mem (U.mul_mem (hSU hx) (hSU hc)) (hSU hx)

theorem outer_weyl_not_normalizer :
    outerFixedWeyl 0∉Subgroup.normalizer (P : Set (originalModelFixed 0)) := by
  apply not_normalizer_of_three_word P (fixedPositive 0) inf_le_left
    (outerInvolution 0) (outerFixedWeyl 0)
    ⟨CFSGReeFFourFixedPositiveFamilies.fixedOuterHom_range_le_fixedPositive 0 ⟨_,rfl⟩,
      outer_mem_derived 0⟩ (outerWeyl_three_word 0)
  intro hw
  exact outerFixedWeyl_not_mem_borel 0 (positive_le_borel 0 hw)

private theorem short_zero (m : ℕ) : shortModelWord m (0 : Fin 16)=1 := rfl

private theorem short_one (m : ℕ) :
    shortModelWord m (1 : Fin 16)=outerFixedWeyl m := by
  change CFSGReeFFourMinimalParabolics.simpleWeyl m false=outerFixedWeyl m
  exact CFSGReeFFourMinimalParabolics.simpleWeyl_false m

private theorem short_two (m : ℕ) :
    shortModelWord m (2 : Fin 16)=middleFixedWeyl m := by
  change CFSGReeFFourMinimalParabolics.simpleWeyl m true=middleFixedWeyl m
  exact CFSGReeFFourMinimalParabolics.simpleWeyl_true m

private theorem normalizer_le_intersection {G : Type*} [Group G]
    (S U : Subgroup G) (hSU : S≤U) (w : G)
    (hw : w∈Subgroup.normalizer (S : Set G)) :
    S≤U⊓U.comap (MulAut.conj w).toMonoidHom := by
  intro x hx
  exact ⟨hSU hx,hSU ((hw x).mp hx)⟩

theorem middle_weyl_not_normalizer :
    middleFixedWeyl 0∉Subgroup.normalizer (P : Set (originalModelFixed 0)) := by
  intro hn
  have hle : P≤shortPositiveIntersection 0 (2 : Fin 16) := by
    simpa only [shortPositiveIntersection,short_two] using
      normalizer_le_intersection P (fixedPositive 0) inf_le_left (middleFixedWeyl 0) hn
  have hf := shortPositiveIntersection_card_factorization 0 (2 : Fin 16)
  have hw : inversionWeight (2 : Fin 16)=2 := by decide +kernel
  rw [fixedPositive_card,hw] at hf
  norm_num at hf
  have hc := Subgroup.card_le_of_le hle
  have hp := positive_card_lower
  omega

private theorem index_zero_of_two_exclusions {G : Type*} [Group G]
    (S : Subgroup G) (w : Fin 16 → G)
    (hsmall : ∀i,w i∈S → i.val≤2) (h1 : w 1∉S) (h2 : w 2∉S)
    (i : Fin 16) (hi : w i∈S) : i=(0 : Fin 16) := by
  have hsmalli := hsmall i hi
  have hcases : i=(0 : Fin 16) ∨ i=(1 : Fin 16) ∨ i=(2 : Fin 16) := by
    rcases (show i.val=0 ∨ i.val=1 ∨ i.val=2 by omega) with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases hcases with h | rfl | rfl
  · exact h
  · exact False.elim (h1 hi)
  · exact False.elim (h2 hi)

theorem normalizing_short_word_eq_zero (i : Fin 16)
    (hi : shortModelWord 0 i∈Subgroup.normalizer (P : Set (originalModelFixed 0))) :
    i=(0 : Fin 16) := by
  have hsmall : ∀j,shortModelWord 0 j∈
      Subgroup.normalizer (P : Set (originalModelFixed 0)) → j.val≤2 :=
    fun j hj => normalizing_shortModelWord_index_le_two P inf_le_left
      ((by decide : 512≤2048).trans positive_card_lower) j hj
  have h1 : shortModelWord 0 1∉Subgroup.normalizer (P : Set (originalModelFixed 0)) := by
    rw [short_one]
    exact outer_weyl_not_normalizer
  have h2 : shortModelWord 0 2∉Subgroup.normalizer (P : Set (originalModelFixed 0)) := by
    rw [short_two]
    exact middle_weyl_not_normalizer
  exact index_zero_of_two_exclusions _ (shortModelWord 0) hsmall h1 h2 i hi

theorem ambientDerivedPositive_normalizer_eq_positive :
    Subgroup.normalizer (P : Set (originalModelFixed 0))=fixedPositive 0 := by
  apply le_antisymm
  · intro g hg
    let N := Subgroup.normalizer (P : Set (originalModelFixed 0))
    have hU : fixedPositive 0≤N := fixedPositive_le_normalizer_ambientDerivedPositive 0
    obtain ⟨u,d,i,v,he⟩ := exists_short_fixed_cell 0 g
    have hd : d.val=1 := by
      have hb : d.val∈(⊥ : Subgroup (originalModelFixed 0)) :=
        (le_of_eq CFSGReeFFourBinaryMiddleGenerators.fixedDiagonal_zero_eq_bot) d.property
      exact Subgroup.mem_bot.mp hb
    have he' : g=u.val*shortModelWord 0 i*v.val := by
      simpa only [hd,mul_one] using he
    have hw : shortModelWord 0 i∈N := by
      have hc : u.val⁻¹*g*v.val⁻¹=shortModelWord 0 i := by rw [he']; group
      exact hc ▸ N.mul_mem (N.mul_mem (N.inv_mem (hU u.property)) hg)
        (N.inv_mem (hU v.property))
    have hi := normalizing_short_word_eq_zero i hw
    have hz : shortModelWord 0 i=1 :=
      (congrArg (shortModelWord 0) hi).trans (short_zero 0)
    have hg' : g=u.val*v.val := by simpa only [hz,mul_one] using he'
    rw [hg']
    exact (fixedPositive 0).mul_mem u.property v.property
  · exact fixedPositive_le_normalizer_ambientDerivedPositive 0

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryExactPositiveNormalizer
