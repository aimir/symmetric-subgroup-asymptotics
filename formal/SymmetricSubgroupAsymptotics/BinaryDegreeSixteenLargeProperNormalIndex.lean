import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenExcessProfile

/-! An original proper normal of rank at least five in a transitive
binary degree-sixteen group has literal index two. This strengthens the
excess-one implication: the whole source may have six generators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- Near saturation of the whole normal rank leaves only one quotient
exponent when the same original normal has an elementary supplement. -/
theorem prime_index_of_elementary_supplement_near_normalRank
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p G) (E N : Subgroup G) [N.Normal]
    (hsup : E ⊔ N = ⊤) (hE : IsMulCommutative E)
    (hexp : ∀ e : E, e ^ p = 1) (hproper : N ≠ ⊤)
    (r : ℕ) (hN : r ≤ MarkedC4.normalGen N)
    (hwhole : MarkedC4.normalGen (⊤ : Subgroup G) ≤ r + 1) : N.index = p := by
  letI : Group.IsNilpotent G := hG.isNilpotent
  obtain ⟨j, hj⟩ := hG.index N
  have hjpos : 0 < j := by
    by_contra he
    have hjzero : j = 0 := by omega
    have hi : N.index = 1 := by simpa only [hjzero, pow_zero] using hj
    exact hproper (Subgroup.index_eq_one.mp hi)
  have heq := normalGen_add_indexExponent_eq_of_elementary_supplement
    p E N hsup hE hexp hG j hj
  obtain ⟨S, hS, hgen⟩ := MarkedC4.genRank_spec (G := G)
  have hchar := (primeCharacterRank_le_generators p S hgen).trans_eq hS
  have htop := MarkedC4.genRank_le_normalGen_top (G := G)
  have hjone : j = 1 := by omega
  simpa only [hjone, pow_one] using hj

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

/-- Full actual top image supplies the literal pair kernel as an
 elementary supplement; no replacement or enlarged normal is used. -/
theorem full_actual_image_proper_normal_five_index_two
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤)
    (hN : 5 ≤ MarkedC4.normalGen N)
    (himage : N.map F.top.rangeRestrict = ⊤) : N.index = 2 := by
  let f := F.top.rangeRestrict
  have hker : f.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  have hsup : F.top.ker ⊔ N = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨n, hn, hng⟩ := show f g ∈ N.map f by rw [himage]; trivial
    have hk : g * n⁻¹ ∈ F.top.ker := by
      rw [← hker]
      change f (g * n⁻¹) = 1
      rw [map_mul, map_inv, hng]
      exact mul_inv_cancel _
    have hprod : (g * n⁻¹) * n ∈ F.top.ker ⊔ N :=
      (F.top.ker ⊔ N).mul_mem
        ((show F.top.ker ≤ F.top.ker ⊔ N from le_sup_left) hk)
        ((show N ≤ F.top.ker ⊔ N from le_sup_right) hn)
    simpa only [inv_mul_cancel_right] using hprod
  have hcomm : IsMulCommutative F.top.ker := IsMulCommutative.of_comm fun a b =>
    F.kernelChart.injective (by rw [map_mul, map_mul, mul_comm])
  have hexp (e : F.top.ker) : e ^ 2 = 1 := by
    apply F.kernelChart.injective
    rw [map_pow, map_one]
    change (2 : ℕ) • (F.kernelChart e).toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  have hdegree : Nat.card X = 16 := by simpa only [Nat.card_fin] using F.card_points
  have hwhole : MarkedC4.normalGen (⊤ : Subgroup U) ≤ 6 := by
    have hb := twoGroup_transitive_normalGen_le_quarter_add_two U hU (⊤ : Subgroup U)
    simpa only [hdegree] using hb
  exact prime_index_of_elementary_supplement_near_normalRank
    2 hU F.top.ker N hsup hcomm hexp hproper 5 hN hwhole

theorem regular_proper_normal_five_index_two
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (N : Subgroup U) [N.Normal]
    (hN : 5 ≤ MarkedC4.normalGen N)
    (hDproper : N.map F.top.rangeRestrict ≠ ⊤) : N.index = 2 := by
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  have hk : f.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have hTop : IsPGroup 2 F.top.range := F.top_isPGroup hU
  have hTopCard : Nat.card F.top.range = 8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T3.exact_card
  have hB : MarkedC4.normalGen (N ⊓ f.ker) ≤ 3 := by
    rw [hk]
    exact F.regular_axis_normalGen_le hU (N ⊓ F.top.ker) inf_le_right hH
  have hD : MarkedC4.normalGen (N.map f) ≤ 2 := by
    have hp := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card (N.map f)
    have hind : 2 ≤ (N.map f).index := (N.map f).one_lt_index_of_ne_top hDproper
    have hc := (N.map f).card_mul_index
    rw [hTopCard] at hc
    have hcard : Nat.card (N.map f) ≤ 4 := by nlinarith
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hp.trans hcard)
  obtain ⟨heq, hBexact, hDexact⟩ :=
    pGroup_actual_intersection_head_additivity_of_saturation
      2 f hf N hU 3 2 (by omega) hB hD
  have hDindex : (N.map f).index = 2 := by
    exact normal_index_two_of_card_eight_normalGen_two hTopCard (N.map f)
      hDproper hDexact.ge
  have hDlarge : 2 < Nat.card (N.map f) := by
    have hc := (N.map f).card_mul_index
    rw [hTopCard, hDindex] at hc
    omega
  have hker : F.top.ker ≤ N := by
    apply F.regular_kernel_le_normal_of_head_equality hU N hH
    · rw [← hk]
      omega
    · exact hDlarge
    · have htransport (K : Subgroup U) [K.Normal] (he : f.ker = K) :
          Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
            Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ K)) +
              Module.finrank (ZMod 2)
                (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ K) N)) := by
        subst K
        exact heq
      exact htransport F.top.ker hk
  exact (F.normal_index_eq_actual_image_index N hker).trans hDindex

theorem heisenberg_proper_normal_five_index_two
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (N : Subgroup U) [N.Normal]
    (hN : 5 ≤ MarkedC4.normalGen N)
    (hDproper : N.map F.top.rangeRestrict ≠ ⊤) : N.index = 2 := by
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  have hk : f.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have hTop : IsPGroup 2 F.top.range := F.top_isPGroup hU
  have hTopCard : Nat.card F.top.range = 32 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T22.exact_card
  have hB : MarkedC4.normalGen (N ⊓ f.ker) ≤ 2 := by
    rw [hk]
    exact F.heisenberg_axis_normalGen_le hU (N ⊓ F.top.ker) inf_le_right hH
  have hD : MarkedC4.normalGen (N.map f) ≤ 3 := by
    have hb := twoGroup_transitive_proper_normalGen_le_quarter_add_one
      F.top.range hTop (N.map f) hDproper
    simpa only [Nat.card_fin] using hb
  obtain ⟨heq, hBexact, hDexact⟩ :=
    pGroup_actual_intersection_head_additivity_of_saturation
      2 f hf N hU 2 3 (by omega) hB hD
  have hDindex : (N.map f).index = 2 := by
    exact transitive_degree_eight_card_thirty_two_normal_index_two
      (X := Fin 8) hTop (by simp only [Nat.card_fin]) hTopCard
      (N.map f) hDproper hDexact.ge
  have hDlarge : 8 < Nat.card (N.map f) := by
    have hc := (N.map f).card_mul_index
    rw [hTopCard, hDindex] at hc
    omega
  have hker : F.top.ker ≤ N := by
    apply F.heisenberg_kernel_le_normal_of_head_equality hU N hH
    · rw [← hk]
      omega
    · exact hDlarge
    · have htransport (K : Subgroup U) [K.Normal] (he : f.ker = K) :
          Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
            Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ K)) +
              Module.finrank (ZMod 2)
                (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ K) N)) := by
        subst K
        exact heq
      exact htransport F.top.ker hk
  exact (F.normal_index_eq_actual_image_index N hker).trans hDindex

end BinaryPairFrame

private theorem map_eq_top_of_same_kernel
    {G Q R : Type} [Group G] [Group Q] [Group R]
    (f : G →* Q) (g : G →* R) (hg : Function.Surjective g)
    (he : f.ker = g.ker) (N : Subgroup G) (hfull : N.map f = ⊤) : N.map g = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨u, rfl⟩ := hg y
  obtain ⟨n, hn, hnu⟩ := show f u ∈ N.map f by rw [hfull]; trivial
  refine ⟨n, hn, ?_⟩
  have hk : u * n⁻¹ ∈ g.ker := by
    rw [← he]
    change f (u * n⁻¹) = 1
    rw [map_mul, map_inv, hnu]
    exact mul_inv_cancel _
  change g (u * n⁻¹) = 1 at hk
  rw [map_mul, map_inv] at hk
  exact (eq_of_mul_inv_eq_one hk).symm

/-- Every proper original rank-five normal in a transitive binary action
of degree sixteen has actual index two, even when the whole source has
six ordinary generators. -/
theorem twoGroup_degree_sixteen_proper_normal_five_index_two
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 16) (N : Subgroup U) [N.Normal]
    (hproper : N ≠ ⊤) (hN : 5 ≤ MarkedC4.normalGen N) : N.index = 2 := by
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 3 U hU hdegree
  by_cases hfull : N.map F.top.rangeRestrict = ⊤
  · exact F.full_actual_image_proper_normal_five_index_two hU N hproper hN hfull
  have hDproper := hfull
  have hreindex (g : Equiv.Perm (Fin 8)) :
      N.map (F.reindex g).top.rangeRestrict ≠ ⊤ := by
    intro hnew
    apply hDproper
    apply map_eq_top_of_same_kernel (F.reindex g).top.rangeRestrict
      F.top.rangeRestrict F.top.rangeRestrict_surjective _ N hnew
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.ker_rangeRestrict, F.reindex_top_ker]
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
    exact (F.reindex g).regular_proper_normal_five_index_two hU hH N hN (hreindex g)
  · let f := F.top.rangeRestrict
    letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f F.top.rangeRestrict_surjective
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
      exact (F.reindex g).heisenberg_proper_normal_five_index_two hU hH N hN (hreindex g)

end SymmetricSubgroupAsymptotics
