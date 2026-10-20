import SymmetricSubgroupAsymptotics.BinaryPairKernelNormalGenerators
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import SymmetricSubgroupAsymptotics.NormalGeneratorActualIntersectionImage
import SymmetricSubgroupAsymptotics.MarkedC4RDTDerivedNormalQuarter
import Mathlib.Data.Fintype.Perm

/-! The exact RDT derived-normal quarter input follows by original-degree
induction, without the finite excess classification. A nonelementary top
uses the proved quarter-module theorem and the smaller derived image.
An elementary top kills that image altogether, so the existing half-module
bound on the original pair labels suffices for the same quarter budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

open BinarySquareActionStructure

private theorem squares_trivial_of_degree_le_two
    {G X : Type} [Group G] [MulAction G X] [Finite X] (hX : Nat.card X ≤ 2) :
    SquaresActTrivially (G := G) (X := X) := by
  have hc : Nat.card (Equiv.Perm X) ∣ 2 := by
    rw [Nat.card_perm]
    rcases (show Nat.card X = 0 ∨ Nat.card X = 1 ∨ Nat.card X = 2 by omega) with h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  intro g x
  have hp : (MulAction.toPermHom G X g) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans hc)
  change (MulAction.toPermHom G X (g ^ 2)) x = x
  rw [map_pow, hp]
  rfl

private theorem commutative_of_squares_trivial
    {G X : Type} [Group G] [MulAction G X] [FaithfulSMul G X]
    (hel : SquaresActTrivially (G := G) (X := X)) : IsMulCommutative G := by
  have hs := squaresActTrivially_iff_pow_two.mp hel
  exact IsMulCommutative.of_comm fun a b =>
    (Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_iff_pow_eq_one.mpr (hs g)) a b).eq

/-- Every actual normal subgroup in the derived group of an original
transitive binary action has normal rank at most a quarter of its degree.
The theorem includes the small abelian actions and has no excess premise. -/
theorem twoGroup_transitive_derived_normalGen_le_quarter
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] (hderived : N ≤ commutator U) :
    MarkedC4.normalGen N ≤ Nat.card X / 4 := by
  suffices hh : ∀ n (X : Type) [Finite X] (U : Subgroup (Equiv.Perm X))
      [MulAction.IsPretransitive U X], IsPGroup 2 U → Nat.card X = n →
      ∀ N : Subgroup U, N.Normal → N ≤ commutator U →
        MarkedC4.normalGen N ≤ Nat.card X / 4 from
    hh _ X U hU rfl N inferInstance hderived
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ U _ hU hn N hN hderived
    letI := hN
    by_cases hsmall : Nat.card X ≤ 2
    · have hc := commutative_of_squares_trivial (squares_trivial_of_degree_le_two
        (G := U) hsmall)
      have hb : N = ⊥ := bot_unique (hderived.trans_eq ((commutator_eq_bot_iff U).mpr hc))
      rw [hb, MarkedC4.normalGen_bot]
      exact Nat.zero_le _
    · have hlarge : 2 < Nat.card X := by omega
      letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      let x : X := Classical.choice inferInstance
      obtain ⟨D⟩ := transitiveBinaryPairCover_nonempty U hU x
      let f : U →* D.Top := D.frame.top.rangeRestrict
      have hf : Function.Surjective f := D.frame.top.rangeRestrict_surjective
      have hk : f.ker = D.frame.top.ker := MonoidHom.ker_rangeRestrict D.frame.top
      letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
      have hmap : (commutator U).map f = commutator D.Top := by
        rw [map_commutator_eq, f.range_eq_top_of_surjective hf]
        rfl
      have hNd : N.map f ≤ commutator D.Top := (Subgroup.map_mono hderived).trans_eq hmap
      have hact : ∀ (u : U) (i : D.Points), u • i = D.frame.top u i := fun _ _ => rfl
      have hdegree := D.degree_product
      by_cases hel : SquaresActTrivially (G := U) (X := D.Points)
      · have htopel : SquaresActTrivially (G := D.Top) (X := D.Points) := by
          intro a i
          obtain ⟨u, rfl⟩ := hf a
          change (f u) ^ 2 • i = i
          rw [← map_pow]
          exact hel u i
        have htopcomm := commutative_of_squares_trivial htopel
        have hbot : N.map f = ⊥ :=
          bot_unique (hNd.trans_eq ((commutator_eq_bot_iff D.Top).mpr htopcomm))
        have hNker : N ≤ D.frame.top.ker := by
          rw [← hk]
          exact (Subgroup.map_eq_bot_iff N).mp hbot
        letI : Nontrivial D.Points :=
          Finite.one_lt_card_iff_nontrivial.mp (by omega)
        have hu : UniformSubrepresentationGeneratorBound
            (permutationFunctionRepresentation (ZMod 2) U D.Points) (Nat.card D.Points / 2) := by
          letI := Fintype.ofFinite D.Points
          apply pGroup_uniformSubrepresentationGeneratorBound_of_head_le hU
          intro M
          exact pGroup_permutationSubrepresentationHead_le_div hU M
        have hb := D.frame.normalGen_le_of_uniform_pair_module hact
          (Nat.card D.Points / 2) hu N hNker
        omega
      · have hkernel : MarkedC4.normalGen (N ⊓ D.frame.top.ker) ≤ Nat.card D.Points / 4 :=
          D.frame.normalGen_le_quarter_of_not_elementary hact hU hel
            (N ⊓ D.frame.top.ker) inf_le_right
        letI := D.top_pretransitive
        have htop := ih (Nat.card D.Points) (by have := D.points_card_lt; omega)
          D.Points D.Top (D.top_isPGroup hU) rfl (N.map f) inferInstance hNd
        have hb := normalGen_le_actual_intersection_add_image f hf N
          (MarkedC4.normalGen (N ⊓ f.ker)) (MarkedC4.normalGen (N.map f)) le_rfl le_rfl
        rw [hk] at hb
        omega

/-- The original published input is now a theorem. Its nonabelian and
n>2 hypotheses are allowed, while the generic proof also handles the
small abelian actions. No other published input is required. -/
theorem publishedDerivedNormalQuarterBinary_proved :
    MarkedC4.RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary := by
  intro n G _hn hG htrans _hnon N hN hderived
  letI := hN
  letI : MulAction.IsPretransitive G (Fin n) := ⟨fun x y => htrans x y⟩
  have hb := twoGroup_transitive_derived_normalGen_le_quarter G hG N hderived
  have hnat : 4 * MarkedC4.normalGen N ≤ n := by
    have hm := Nat.div_mul_le_self n 4
    have hb' : MarkedC4.normalGen N ≤ n / 4 := by simpa only [Nat.card_fin] using hb
    exact (Nat.mul_le_mul_left 4 hb').trans (by simpa only [mul_comm] using hm)
  have hreal : (4 : ℝ) * (MarkedC4.normalGen N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
  linarith

end SymmetricSubgroupAsymptotics
