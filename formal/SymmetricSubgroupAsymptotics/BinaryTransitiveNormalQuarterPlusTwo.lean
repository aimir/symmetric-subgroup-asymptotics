import SymmetricSubgroupAsymptotics.BinaryNormalDegreeRecurrence
import SymmetricSubgroupAsymptotics.PermutationTwoGroupRank
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame

/-! The universal excess-two ceiling is intrinsic to original binary
permutation actions. The finite exceptional cutoff and the proper-normal
profiles are separate obligations; no such classifier is assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

open BinarySquareActionStructure

/-- All actual ambient normal subgroups have the universal excess-two
ceiling, independently of the degree or any finite classification. -/
theorem twoGroup_transitive_normalGen_le_quarter_add_two
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N ≤ Nat.card X / 4 + 2 := by
  suffices hh : ∀ n (X : Type) [Finite X] (U : Subgroup (Equiv.Perm X))
      [MulAction.IsPretransitive U X], IsPGroup 2 U → Nat.card X = n →
      ∀ N : Subgroup U, N.Normal → MarkedC4.normalGen N ≤ Nat.card X / 4 + 2 from
    hh _ X U hU rfl N inferInstance
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ U _ hU hn N hN
    letI := hN
    by_cases hsmall : Nat.card X ≤ 8
    · have hNp : IsPGroup 2 N := hU.to_subgroup N
      have hhalf := (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank 2 N hNp).trans
        (permutationTwoGroup_primeCharacterRank_le N X hNp)
      omega
    · have hlarge : 8 < Nat.card X := by omega
      letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      let x : X := Classical.choice inferInstance
      obtain ⟨D⟩ := transitiveBinaryPairCover_nonempty U hU x
      have hact : ∀ (u : U) (i : D.Points), u • i = D.frame.top u i := fun _ _ => rfl
      have hdegree := D.degree_product
      let f := D.frame.top.rangeRestrict
      letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f
        D.frame.top.rangeRestrict_surjective
      by_cases hel : SquaresActTrivially (G := U) (X := D.Points)
      · obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hU
          (MulAction.stabilizer U D.base) ⊤ le_top
        have hcard : Nat.card D.Points = 2 ^ s.length := by
          simpa only [Subgroup.relIndex_top_right,
            MulAction.index_stabilizer_of_transitive U D.base] using s.relIndex
        have hk : 3 ≤ s.length := by
          by_contra he
          have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
            (by omega : s.length ≤ 2)
          rw [← hcard] at hp
          norm_num at hp
          omega
        by_cases hwide : 5 ≤ s.length
        · have hb := D.frame.normalGen_le_half_label_degree_of_elementary_top
            hact hU hel D.base s.length hwide hcard N
          omega
        · have hb := D.frame.normalGen_le_middle_add_exponent_of_elementary_top
            hact hU hel D.base s.length hcard N
          have hs : s.length = 3 ∨ s.length = 4 := by omega
          rcases hs with hs | hs
          · rw [hs] at hcard hb
            norm_num [Nat.choose] at hcard hb
            omega
          · rw [hs] at hcard hb
            norm_num [Nat.choose] at hcard hb
            omega
      · letI := D.top_pretransitive
        have htop := ih (Nat.card D.Points) (by have := D.points_card_lt; omega)
          D.Points D.Top (D.top_isPGroup hU) rfl (N.map f) inferInstance
        have hb := D.frame.normalGen_le_quarter_add_actual_top hact hU hel N
        change MarkedC4.normalGen N ≤ Nat.card D.Points / 4 + MarkedC4.normalGen (N.map f) at hb
        omega

/-- Coarse sixteen-point normal ranks require no normal registry. -/
theorem twoGroup_degree_sixteen_normalGen_le_six
    (U : Subgroup (Equiv.Perm (Fin 16))) [MulAction.IsPretransitive U (Fin 16)]
    (hU : IsPGroup 2 U) (N : Subgroup U) [N.Normal] : MarkedC4.normalGen N ≤ 6 := by
  simpa only [Nat.card_fin] using twoGroup_transitive_normalGen_le_quarter_add_two U hU N

/-- The degree32 excess-two ceiling is likewise unconditional for every
actual normal subgroup, without enumerating degree32 groups. -/
theorem twoGroup_degree_thirtytwo_normalGen_le_ten
    (U : Subgroup (Equiv.Perm (Fin 32))) [MulAction.IsPretransitive U (Fin 32)]
    (hU : IsPGroup 2 U) (N : Subgroup U) [N.Normal] : MarkedC4.normalGen N ≤ 10 := by
  simpa only [Nat.card_fin] using twoGroup_transitive_normalGen_le_quarter_add_two U hU N

end SymmetricSubgroupAsymptotics
