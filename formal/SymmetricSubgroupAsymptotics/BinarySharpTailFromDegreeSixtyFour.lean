import SymmetricSubgroupAsymptotics.BinaryNormalDegreeRecurrence
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing

/-! The sharp large-degree tail uses only the degree-sixty-four case.
The actual original normal top image is retained at every induction step.
Neither the published excess proposition nor its conclusion is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem twoGroup_transitive_normalGen_le_quarter_of_degree_sixtyfour
    (h64 : ∀ (Y : Type) [Finite Y] (V : Subgroup (Equiv.Perm Y))
      [MulAction.IsPretransitive V Y], IsPGroup 2 V → Nat.card Y = 64 →
      ∀ N : Subgroup V, N.Normal → MarkedC4.normalGen N ≤ 16)
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hlarge : 64 ≤ Nat.card X) (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N ≤ Nat.card X / 4 := by
  suffices hh : ∀ n (X : Type) [Finite X] (U : Subgroup (Equiv.Perm X))
      [MulAction.IsPretransitive U X], IsPGroup 2 U → Nat.card X = n →
      64 ≤ Nat.card X → ∀ N : Subgroup U, N.Normal →
        MarkedC4.normalGen N ≤ Nat.card X / 4 from
    hh _ X U hU rfl hlarge N inferInstance
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ U _ hU hn hlarge N hN
    letI := hN
    by_cases hbase : Nat.card X = 64
    · simpa only [hbase] using h64 X U hU hbase N hN
    · have hbig : 64 < Nat.card X := by omega
      letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      let x : X := Classical.choice inferInstance
      obtain ⟨D⟩ := transitiveBinaryPairCover_nonempty U hU x
      have hact : ∀ (u : U) (i : D.Points), u • i = D.frame.top u i := fun _ _ => rfl
      have hdegree := D.degree_product
      obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hU
        (MulAction.stabilizer U D.base) ⊤ le_top
      have hcard : Nat.card D.Points = 2 ^ s.length := by
        simpa only [Subgroup.relIndex_top_right,
          MulAction.index_stabilizer_of_transitive U D.base] using s.relIndex
      have hk : 6 ≤ s.length := by
        by_contra he
        have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
          (by omega : s.length ≤ 5)
        rw [← hcard] at hp
        norm_num at hp
        omega
      have hpoints : 64 ≤ Nat.card D.Points := by
        have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hk
        rw [← hcard] at hp
        norm_num at hp
        exact hp
      have hmod : Nat.card D.Points % 4 = 0 := by
        rw [hcard, show s.length = 2 + (s.length - 2) by omega, pow_add]
        norm_num [Nat.mul_mod]
      by_cases hel : BinarySquareActionStructure.SquaresActTrivially (G := U) (X := D.Points)
      · have hb := D.frame.normalGen_le_half_label_degree_of_elementary_top
          hact hU hel D.base s.length (by omega) hcard N
        omega
      · let f := D.frame.top.rangeRestrict
        letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f
          D.frame.top.rangeRestrict_surjective
        letI := D.top_pretransitive
        have ht := ih (Nat.card D.Points) (by have := D.points_card_lt; omega)
          D.Points D.Top (D.top_isPGroup hU) rfl hpoints (N.map f) inferInstance
        have hb := D.frame.normalGen_le_quarter_add_actual_top hact hU hel N
        change MarkedC4.normalGen N ≤ Nat.card D.Points / 4 +
          MarkedC4.normalGen (N.map f) at hb
        omega

end SymmetricSubgroupAsymptotics
