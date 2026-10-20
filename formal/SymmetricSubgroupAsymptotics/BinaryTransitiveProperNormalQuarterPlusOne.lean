import SymmetricSubgroupAsymptotics.BinaryProperNormalRankSaving
import SymmetricSubgroupAsymptotics.BinaryTransitiveNormalQuarterPlusTwo

/-! Every proper original normal subgroup satisfies the universal
excess-one ceiling. Full-top normals use their actual elementary kernel
supplement, and proper-top normals retain their proper actual image.
No finite permutation-group census enters this induction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

open BinarySquareActionStructure

private theorem proper_elementary_image_middle_bound
    {X I : Type} [Finite X] [Finite I]
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I) [MulAction U I]
    [MulAction.IsPretransitive U I]
    (hact : ∀ (u : U) (i : I), u • i = F.top u i) (hU : IsPGroup 2 U)
    (hel : SquaresActTrivially (G := U) (X := I))
    (i₀ : I) (k : ℕ) (hcard : Nat.card I = 2 ^ k)
    (N : Subgroup U) [N.Normal] (hproper : N.map F.top.rangeRestrict ≠ ⊤) :
    MarkedC4.normalGen N + 1 ≤ k.choose (k / 2) + k := by
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  letI : MulAction.IsPretransitive F.top.range I := ⟨fun i j => by
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U i j
    refine ⟨f u, ?_⟩
    change F.top u i = j
    rw [← hact]
    exact hu⟩
  have htopel : SquaresActTrivially (G := F.top.range) (X := I) := by
    intro a i
    obtain ⟨u, rfl⟩ := hf a
    change (f u) ^ 2 • i = i
    rw [← map_pow]
    change F.top (u ^ 2) i = i
    rw [← hact]
    exact hel u i
  have htop := elementary_transitive_proper_normalGen_add_one_le_exponent
    htopel i₀ k hcard (N.map f) hproper
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U I) (k.choose (k / 2)) := by
    letI := Fintype.ofFinite I
    apply pGroup_uniformSubrepresentationGeneratorBound_of_head_le hU
    intro M
    exact twoGroup_permutationSubrepresentationHead_le_width hU k hcard i₀ M
  have hb := F.normalGen_le_uniform_add_actual_top hact _ hu N
  change MarkedC4.normalGen N ≤ k.choose (k / 2) + MarkedC4.normalGen (N.map f) at hb
  omega

/-- Proper normals in the original faithful transitive binary action
have excess at most one, at every degree. -/
theorem twoGroup_transitive_proper_normalGen_le_quarter_add_one
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤) :
    MarkedC4.normalGen N ≤ Nat.card X / 4 + 1 := by
  suffices hh : ∀ n (X : Type) [Finite X] (U : Subgroup (Equiv.Perm X))
      [MulAction.IsPretransitive U X], IsPGroup 2 U → Nat.card X = n →
      ∀ N : Subgroup U, N.Normal → N ≠ ⊤ →
        MarkedC4.normalGen N ≤ Nat.card X / 4 + 1 from
    hh _ X U hU rfl N inferInstance hproper
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ U _ hU hn N hN hproper
    letI := hN
    by_cases hsmall : Nat.card X ≤ 2
    · have hNp : IsPGroup 2 N := hU.to_subgroup N
      have hhalf := (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank 2 N hNp).trans
        (permutationTwoGroup_primeCharacterRank_le N X hNp)
      omega
    · letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      let x : X := Classical.choice inferInstance
      obtain ⟨D⟩ := transitiveBinaryPairCover_nonempty U hU x
      have hact : ∀ (u : U) (i : D.Points), u • i = D.frame.top u i := fun _ _ => rfl
      have hdegree := D.degree_product
      let f := D.frame.top.rangeRestrict
      letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f
        D.frame.top.rangeRestrict_surjective
      by_cases hfull : N.map f = ⊤
      · have hsave := D.frame.normalGen_add_one_le_top_of_full_actual_image hU N hfull hproper
        have hwhole := twoGroup_transitive_normalGen_le_quarter_add_two U hU (⊤ : Subgroup U)
        omega
      · by_cases hel : SquaresActTrivially (G := U) (X := D.Points)
        · obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hU
            (MulAction.stabilizer U D.base) ⊤ le_top
          have hcard : Nat.card D.Points = 2 ^ s.length := by
            simpa only [Subgroup.relIndex_top_right,
              MulAction.index_stabilizer_of_transitive U D.base] using s.relIndex
          by_cases hwide : 5 ≤ s.length
          · have hb := D.frame.normalGen_le_half_label_degree_of_elementary_top
              hact hU hel D.base s.length hwide hcard N
            omega
          · have hb := proper_elementary_image_middle_bound D.frame hact hU hel
              D.base s.length hcard N hfull
            have hk : 1 ≤ s.length := by
              by_contra he
              have heq : s.length = 0 := by omega
              rw [heq] at hcard
              norm_num at hcard
              omega
            have hs : s.length = 1 ∨ s.length = 2 ∨ s.length = 3 ∨ s.length = 4 := by omega
            rcases hs with hs | hs | hs | hs <;>
              rw [hs] at hcard hb <;> norm_num [Nat.choose] at hcard hb <;> omega
        · letI := D.top_pretransitive
          have htop := ih (Nat.card D.Points) (by have := D.points_card_lt; omega)
            D.Points D.Top (D.top_isPGroup hU) rfl (N.map f) inferInstance hfull
          have hb := D.frame.normalGen_le_quarter_add_actual_top hact hU hel N
          change MarkedC4.normalGen N ≤ Nat.card D.Points / 4 + MarkedC4.normalGen (N.map f) at hb
          omega

/-- The proper degree-eight bound is intrinsic, with no finite normal table. -/
theorem twoGroup_degree_eight_proper_normalGen_le_three
    (U : Subgroup (Equiv.Perm (Fin 8))) [MulAction.IsPretransitive U (Fin 8)]
    (hU : IsPGroup 2 U) (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤) :
    MarkedC4.normalGen N ≤ 3 := by
  simpa only [Nat.card_fin] using
    twoGroup_transitive_proper_normalGen_le_quarter_add_one U hU N hproper

end SymmetricSubgroupAsymptotics
