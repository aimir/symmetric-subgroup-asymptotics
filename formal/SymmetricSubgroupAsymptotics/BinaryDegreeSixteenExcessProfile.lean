import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenLiteralTopExcess
import SymmetricSubgroupAsymptotics.BinaryDegreeEightElementaryActionCoverage
import SymmetricSubgroupAsymptotics.BinaryDegreeEightProperActionCoverage
import SymmetricSubgroupAsymptotics.BinaryPairFrameConjugateTop

/-! The exact degree-sixteen RDT5.3 packet. Only degree-eight point-action
coverage and complete eight-dimensional natural-module certificates are
used. The original degree-sixteen group, its proper normal subgroup, and
its actual pair kernel stay identified through every point relabeling. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics

/-- A rank-five proper original normal requires six ordinary generators
in the original degree-sixteen source. -/
theorem twoGroup_degree_sixteen_six_le_genRank_of_proper_normal_five
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 16) (N : Subgroup U) [N.Normal]
    (hproper : N ≠ ⊤) (hN : 5 ≤ MarkedC4.normalGen N) :
    6 ≤ MarkedC4.genRank U := by
  by_contra hbad
  have hgen : MarkedC4.genRank U ≤ 5 := by omega
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 3 U hU hdegree
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have hTop : IsPGroup 2 F.top.range := F.top_isPGroup hU
  have htrans : ∀ i j : Fin 8, ∃ t : F.top.range, t.val i = j := by
    intro i j
    exact MulAction.exists_smul_eq F.top.range i j
  letI : MulAction U (Fin 8) := {
    smul := fun u i => F.top u i
    one_smul := by intro i; change F.top 1 i = i; rw [map_one]; rfl
    mul_smul := by
      intro u v i
      change F.top (u * v) i = F.top u (F.top v i)
      rw [map_mul]
      rfl }
  have hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i := fun _ _ => rfl
  letI : MulAction.IsPretransitive U (Fin 8) := ⟨fun i j => by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    exact ⟨u, ht⟩⟩
  by_cases hel : BinarySquareActionStructure.SquaresActTrivially (G := U) (X := Fin 8)
  · have htopel : BinarySquareActionStructure.SquaresActTrivially
        (G := F.top.range) (X := Fin 8) := by
      intro t i
      obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
      rw [← map_pow]
      exact hel u i
    obtain ⟨g, hg⟩ := BinaryDegreeEightElementaryActionCoverage.elementary_action_conjugate_regular
      F.top.range hTop htrans htopel
    have hH : (F.reindex g).top.range =
        Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) :=
      (F.reindex_top_range_conjugation g).trans hg
    exact hbad ((F.reindex g).regular_six_le_genRank_of_proper_normal_five hU hH N hproper hN)
  · let f := F.top.rangeRestrict
    letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f F.top.rangeRestrict_surjective
    have hDproper : N.map f ≠ ⊤ := by
      intro hfull
      have hb := F.normalGen_add_one_le_top_of_full_actual_image hU N hfull hproper
      have ht := MarkedC4.ActualExcessOneQuotientRank.normalGen_top_le_genRank U
      omega
    rcases BinaryDegreeEightProperActionCoverage.proper_normal_bounds_or_heisenberg_action
      F.top.range hTop htrans with hsmall | ⟨g, hg⟩
    · have hD := hsmall (N.map f) hDproper
      have hb := F.normalGen_le_quarter_add_actual_top hact hU hel N
      change MarkedC4.normalGen N ≤ Nat.card (Fin 8) / 4 +
        MarkedC4.normalGen (N.map f) at hb
      norm_num only [Nat.card_fin] at hb
      omega
    · have hH : (F.reindex g).top.range =
          Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) :=
        (F.reindex_top_range_conjugation g).trans hg
      exact hbad ((F.reindex g).heisenberg_six_le_genRank_of_proper_normal_five hU hH N hproper hN)

end SymmetricSubgroupAsymptotics

namespace SymmetricSubgroupAsymptotics.BinaryDegreeSixteenExcessProfile

open MarkedC4 MarkedC4.RDTExcessStructure

/-- Only the original whole group is excessive in excess-one degree16. -/
theorem only_whole_of_excess_one
    (G : Subgroup (Equiv.Perm (Fin 16))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 16 1)
    (N : Subgroup G) [N.Normal] (hhigh : (16 : ℝ) / 4 < normalGen N) : N = ⊤ := by
  letI : MulAction.IsPretransitive G (Fin 16) := ⟨htrans⟩
  letI : Group.IsNilpotent G := hG.isNilpotent
  have hwhole := hexcess.2 (⊤ : Subgroup G) inferInstance
  norm_num at hwhole hhigh
  have hwholeNat : normalGen (⊤ : Subgroup G) ≤ 5 := by exact_mod_cast hwhole
  have hgen := MarkedC4.genRank_le_normalGen_top (G := G)
  by_contra hproper
  have hNsmall : 4 < normalGen N := by exact_mod_cast hhigh
  have hN : 5 ≤ normalGen N := by omega
  have hsix := twoGroup_degree_sixteen_six_le_genRank_of_proper_normal_five
    G hG (by simp only [Nat.card_fin]) N hproper hN
  omega

/-- Full exact h53 conclusion at degree16, with no published excess input. -/
theorem proposition53_degree_sixteen
    (G : Subgroup (Equiv.Perm (Fin 16))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hhigh : ∃ N : Subgroup G, N.Normal ∧ (16 : ℝ) / 4 < normalGen N) :
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧ HasExcess G 16 i ∧ 16 ≤ 32 ∧
      (i = 1 → ∀ N : Subgroup G, N.Normal → (16 : ℝ) / 4 < normalGen N → N = ⊤) ∧
      (i = 2 → 16 = 8 ∨ 16 = 16 ∨ 16 = 32) := by
  letI : MulAction.IsPretransitive G (Fin 16) := ⟨htrans⟩
  have hall (N : Subgroup G) [N.Normal] : normalGen N ≤ 6 := by
    simpa only [Nat.card_fin] using twoGroup_transitive_normalGen_le_quarter_add_two G hG N
  by_cases hsix : ∃ N : Subgroup G, N.Normal ∧ normalGen N = 6
  · have hexcess : HasExcess G 16 2 := by
      constructor
      · obtain ⟨N, hN, hval⟩ := hsix
        exact ⟨N, hN, by norm_num [hval]⟩
      · intro N hN
        letI := hN
        norm_num
        exact hall N
    exact ⟨2, Or.inr rfl, hexcess, by decide, by intro h; omega,
      fun _ => Or.inr (Or.inl rfl)⟩
  · have hfive (N : Subgroup G) [N.Normal] : normalGen N ≤ 5 := by
      have hb := hall N
      have hne : normalGen N ≠ 6 := fun he => hsix ⟨N, inferInstance, he⟩
      omega
    have hexcess : HasExcess G 16 1 := by
      constructor
      · obtain ⟨N, hN, hval⟩ := hhigh
        letI := hN
        have hb := hfive N
        norm_num at hval
        have heq : normalGen N = 5 := by omega
        exact ⟨N, hN, by norm_num [heq]⟩
      · intro N hN
        letI := hN
        norm_num
        exact hfive N
    refine ⟨1, Or.inl rfl, hexcess, by decide, ?_, fun _ => Or.inr (Or.inl rfl)⟩
    intro _ N hN hval
    letI := hN
    exact only_whole_of_excess_one G hG htrans hexcess N hval

end SymmetricSubgroupAsymptotics.BinaryDegreeSixteenExcessProfile
