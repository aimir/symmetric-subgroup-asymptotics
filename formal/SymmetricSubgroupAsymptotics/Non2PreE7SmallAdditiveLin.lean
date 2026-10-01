import SymmetricSubgroupAsymptotics.Non2PreE7LinearThreeGroup
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveS4

/-!
# LIN: `SL₂(3)` and `GL₂(3)` on their eight nonzero vectors (D0387)

The family is exactly these two actual degree-eight actions.

* **GL mode.**  Every nontrivial normal subgroup contains `{±I}`, so the
  nontrivial literal quotients are quotients of `S₄ = PGL₂(3)` on the four
  lines.  Onto maps to `GL₂(3)` lift onto maps to `S₄` through the central
  kernel: `|Epi(J, GL₂(3))| ≤ |Epi(J, S₄)| · |Hom(J, C₂)| ≤ C 2^(3b/4)`.
* **SL mode.**  The comparator is `A₄ × C₂` on `4 + 2` points.  Nontrivial
  quotients are quotients of `A₄`; onto maps to `SL₂(3)` give, with the
  binary characters of the source, onto maps to `A₄ × C₂` or `A₄`:
  `|Epi(J, SL₂(3))| ≤ Z_J(A₄ × C₂)`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace LinearThree

open Equiv NaturalS4

/-! ## The Klein subgroup of `A₄` -/

/-- `V₄` inside `A₄`. -/
def kleinA4 : Subgroup a4 := klein.comap a4.subtype

instance kleinA4_normal : kleinA4.Normal :=
  ⟨fun v hv g => kleinSet_conj (g : Perm (Fin 4)) v hv⟩

theorem kleinA4_minimal (W : Subgroup a4) (hW : W.Normal) (hWV : W ≤ kleinA4) :
    W = ⊥ ∨ W = kleinA4 := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hb
  have hw1' : (w : Perm (Fin 4)) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  apply le_antisymm hWV
  intro v hv
  by_cases hv1 : (v : Perm (Fin 4)) = 1
  · rw [show v = 1 from Subtype.ext hv1]
    exact W.one_mem
  obtain ⟨g, hg, hgv⟩ := klein_a4_transitive _ (hWV hwW) hw1' _ hv hv1
  have := hW.conj_mem w hwW ⟨g, hg⟩
  convert this using 1
  exact Subtype.ext hgv.symm

theorem kleinA4_selfCentralizing (x : a4) (hx : ∀ v ∈ kleinA4, x * v = v * x) :
    x ∈ kleinA4 := by
  have hc : ∀ v (hv : v ∈ kleinSet), (x : Perm (Fin 4)) * v = v * x := by
    intro v hv
    have := hx ⟨v, kleinSet_sub_a4Set v hv⟩ hv
    exact congrArg Subtype.val this
  exact centralizer_kleinSet _ (hc c1 (by decide)) (hc c2 (by decide)) (hc c3 (by decide))

theorem a4_eq_prod_order_three : ∀ g ∈ a4Set, ∃ u ∈ a4Set, ∃ v ∈ a4Set,
    u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ g = u * v := by decide

/-- `A₄` has no binary character. -/
theorem a4_no_binary_character (χ : a4 →* Multiplicative (ZMod 2)) : χ = 1 := by
  have h3 : ∀ x : Multiplicative (ZMod 2), x ^ 3 = 1 → x = 1 := by decide
  ext g
  obtain ⟨u, hu, v, hv, hu3, hv3, huv⟩ := a4_eq_prod_order_three g g.2
  have hg : g = ⟨u, hu⟩ * ⟨v, hv⟩ := Subtype.ext huv
  have hU : χ ⟨u, hu⟩ = 1 := h3 _ (by
    rw [← map_pow]
    rw [show (⟨u, hu⟩ : a4) ^ 3 = 1 from Subtype.ext hu3, map_one])
  have hV : χ ⟨v, hv⟩ = 1 := h3 _ (by
    rw [← map_pow]
    rw [show (⟨v, hv⟩ : a4) ^ 3 = 1 from Subtype.ext hv3, map_one])
  rw [hg, map_mul, hU, hV, one_mul]
  rfl

/-! ## The SL normal menu -/

theorem normal_cover_SL (N : Subgroup SL3) (hN : N.Normal) (hNb : N ≠ ⊥) :
    projectiveSL.ker ≤ N := by
  have hneg : ∃ g ∈ N, ((g : GL3) : M2) = -1 := by
    by_cases hmap : N.map projectiveSL = ⊥
    · obtain ⟨⟨g, hgN⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNb
      have hg1' : (g : GL3) ≠ 1 := fun h => hg1 (Subtype.ext (Subtype.ext h))
      have hgker : (g : GL3) ∈ projective.ker := by
        rw [← mem_ker_projectiveSL, MonoidHom.mem_ker]
        have : projectiveSL g ∈ N.map projectiveSL := ⟨g, hgN, rfl⟩
        rw [hmap] at this
        exact (Subgroup.mem_bot).mp this
      rcases (mem_ker_projective _).mp hgker with h | h
      · exact absurd (Units.ext h) hg1'
      · exact ⟨g, hgN, h⟩
    · haveI : (N.map projectiveSL).Normal := hN.map _ projectiveSL_surjective
      have hk := le_of_minimal_selfCentralizing kleinA4 kleinA4_minimal
        kleinA4_selfCentralizing (N.map projectiveSL) hmap
      obtain ⟨g, hgN, hg⟩ := hk (show (⟨c1, kleinSet_sub_a4Set c1 (by decide)⟩ : a4) ∈ kleinA4
        by exact (show c1 ∈ kleinSet by decide))
      refine ⟨g * g, N.mul_mem hgN hgN, ?_⟩
      show (((g : GL3) * (g : GL3) : GL3) : M2) = -1
      rw [Units.val_mul]
      refine sq_of_c1 _ (coe_mem_glSet _) (fun ℓ => ?_)
      have := congrArg (fun σ : a4 => (σ : Perm (Fin 4)) ℓ) hg
      exact this
  obtain ⟨g, hgN, hg⟩ := hneg
  intro x hx
  rcases (mem_ker_projective _).mp ((mem_ker_projectiveSL x).mp hx) with h | h
  · rw [show x = 1 from Subtype.ext (Units.ext h)]
    exact N.one_mem
  · rw [show x = g from Subtype.ext (Units.ext (h.trans hg.symm))]
    exact hgN

theorem card_ker_projectiveSL : Nat.card projectiveSL.ker = 2 := by
  have hneg : (-1 : M2) ∈ glSet := by decide
  have hnegSL : ofGL (-1) hneg ∈ slSub :=
    (mem_slSub _).mpr (by exact (by decide : (-1 : M2) ∈ slSet))
  let m : SL3 := ⟨ofGL (-1) hneg, hnegSL⟩
  have hm : m ∈ projectiveSL.ker :=
    (mem_ker_projectiveSL m).mpr ((mem_ker_projective _).mpr (Or.inr rfl))
  have hm1 : m ≠ 1 := by
    intro h
    have := congrArg (fun g : SL3 => ((g : GL3) : M2)) h
    simp only [m, coe_ofGL] at this
    revert this
    decide
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨m, hm⟩, fun h => hm1 (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨x, hx⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases hx1 : x = 1
  · left
    exact Subtype.ext hx1
  · right
    apply Subtype.ext
    apply Subtype.ext
    have hx1' : (x : GL3) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hm1' : (m : GL3) ≠ 1 := fun h => hm1 (Subtype.ext h)
    exact eq_of_ker_ne_one ((mem_ker_projectiveSL x).mp hx) ((mem_ker_projectiveSL m).mp hm)
      hx1' hm1'

/-! ## The comparator `A₄ × C₂` -/

/-- `A₄ × C₂` on `4 + 2` points. -/
def a4c2Action : a4 × Multiplicative (ZMod 2) →* Perm (Fin (4 + (1 + 1))) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 4)) finSumFinEquiv).trans finSumFinEquiv).permCongrHom.toMonoidHom.comp
    ((Perm.sumCongrHom (Fin 4) (Fin 1 ⊕ Fin 1)).comp
      (a4.subtype.prodMap (C2Wreath.blockSwap (Fin 1))))

theorem a4c2Action_injective : Function.Injective a4c2Action := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : (Perm.sumCongrHom (Fin 4) (Fin 1 ⊕ Fin 1))
      ((a4.subtype.prodMap (C2Wreath.blockSwap (Fin 1))) x) = 1 := by
    apply (((Equiv.sumCongr (Equiv.refl (Fin 4)) finSumFinEquiv).trans
      finSumFinEquiv).permCongrHom).injective
    rw [map_one]
    exact hx
  have h2 := Perm.sumCongrHom_injective (h1.trans (map_one _).symm)
  have ha : (x.1 : Perm (Fin 4)) = 1 := congrArg Prod.fst h2
  have hb : C2Wreath.blockSwap (Fin 1) x.2 = 1 := congrArg Prod.snd h2
  refine Prod.ext (Subtype.ext ha) ?_
  rcases C2Wreath.cases x.2 with h | h
  · exact h
  · exfalso
    rw [h, C2Wreath.blockSwap] at hb
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, C2Wreath.gen_ne_one, if_false] at hb
    have := congrArg (fun σ : Perm (Fin 1 ⊕ Fin 1) => σ (Sum.inl 0)) hb
    simp at this

/-- Onto maps to `SL₂(3)` lift onto maps to `A₄` with a binary character. -/
theorem sl_lift {b : ℕ} (J : Subgroup (Perm (Fin b))) :
    Nat.card (GroupEpimorphism J SL3) ≤
      Nat.card (GroupEpimorphism J a4) * Nat.card (J →* Multiplicative (ZMod 2)) := by
  have hlift := epi_card_le_centralLift (J := J) projectiveSL projectiveSL_surjective
    central_of_kerSL
  have e : projectiveSL.ker ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (p := 2) card_ker_projectiveSL
      ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)).trans
        (Nat.card_zmod 2))
  have hker : Nat.card (J →* projectiveSL.ker) = Nat.card (J →* Multiplicative (ZMod 2)) :=
    Nat.card_congr
      { toFun := fun f => e.toMonoidHom.comp f
        invFun := fun f => e.symm.toMonoidHom.comp f
        left_inv := fun f => MonoidHom.ext fun x => e.symm_apply_apply (f x)
        right_inv := fun f => MonoidHom.ext fun x => e.apply_symm_apply (f x) }
  rw [hker] at hlift
  exact hlift

/-- The binary factor axis `⊥ × C₂` of `A₄ × C₂`. -/
def a4c2FstAxis : Subgroup (a4 × Multiplicative (ZMod 2)) := (MonoidHom.fst _ _).ker

instance : a4c2FstAxis.Normal := MonoidHom.normal_ker _

theorem a4c2FstAxis_ne_bot : (⊥ : Subgroup (a4 × Multiplicative (ZMod 2))) ≠ a4c2FstAxis := by
  intro h
  have hmem : ((1 : a4), C2Wreath.gen) ∈ a4c2FstAxis := by
    show ((1 : a4), C2Wreath.gen).1 = 1
    rfl
  rw [← h] at hmem
  have := congrArg Prod.snd ((Subgroup.mem_bot).mp hmem)
  exact C2Wreath.gen_ne_one this

/-- `(A₄ × C₂) / (⊥ × C₂) ≅ A₄`. -/
def a4c2FstQuotient : a4 ≃* (a4 × Multiplicative (ZMod 2)) ⧸ a4c2FstAxis :=
  (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.fst a4 (Multiplicative (ZMod 2)))
    Prod.fst_surjective).symm

/-- The two axes `⊥` and `⊥ × C₂` of `A₄ × C₂`. -/
theorem a4c2_axes {b : ℕ} (J : Subgroup (Perm (Fin b))) :
    Nat.card (GroupEpimorphism J (a4 × Multiplicative (ZMod 2))) +
        Nat.card (GroupEpimorphism J a4) ≤
      completeQuotientCount (R := a4 × Multiplicative (ZMod 2)) J :=
  two_axes_le_completeQuotientCount J ⟨⊥, inferInstance⟩ ⟨a4c2FstAxis, inferInstance⟩
    (fun h => a4c2FstAxis_ne_bot (congrArg Subtype.val h))
    (QuotientGroup.quotientBot.symm) a4c2FstQuotient

/-- `|Epi(J, SL₂(3))| ≤ Z_J(A₄ × C₂)`. -/
theorem slBottom_le {b : ℕ} (J : Subgroup (Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J SL3) : ℝ) ≤
      1 * completeQuotientWeight (R := a4 × Multiplicative (ZMod 2)) J +
        0 * (2 : ℝ) ^ ((0 : ℝ) * b) := by
  rw [one_mul, zero_mul, add_zero]
  have hnat : Nat.card (GroupEpimorphism J SL3) ≤
      completeQuotientCount (R := a4 × Multiplicative (ZMod 2)) J :=
    (sl_lift J).trans ((epi_mul_hom_two_le (J := J) a4_no_binary_character).trans
      (a4c2_axes J))
  show (Nat.card (GroupEpimorphism J SL3) : ℝ) ≤
    (completeQuotientCount (R := a4 × Multiplicative (ZMod 2)) J : ℝ)
  exact_mod_cast hnat

end LinearThree

namespace Non2UnipotentPrefixFiniteMenu

open Equiv LinearThree

/-- The LIN family with the selected literal action and its relabelling
retained as data. -/
inductive PreE7LinSource (w : ℕ) (i : PreE7NonPairActionClass w) : Type
  | gl (chart : NV ≃ Fin w)
      (action_eq : preE7NonPairAction w i = relabelSubgroup chart natural.range)
  | sl (chart : NV ≃ Fin w)
      (action_eq : preE7NonPairAction w i =
        relabelSubgroup chart (natural.comp slSub.subtype).range)

theorem lin_width {w : ℕ} (e : NV ≃ Fin w) : w = 8 := by
  rw [width_eq_of_relabel e, card_NV]

/-- The GL mode: comparator `S₄` on the four lines. -/
def linGLModel {w : ℕ} (i : PreE7NonPairActionClass w) (e : NV ≃ Fin w)
    (h : preE7NonPairAction w i = relabelSubgroup e natural.range) :
    PreE7NormalComparatorModel w i where
  G := GL3
  equiv := relabelModelEquiv natural natural_injective e h
  index := Unit
  R := Perm (Fin 4)
  degree := 4
  action := MonoidHom.id _
  action_injective := Function.injective_id
  proj := fun _ => projective
  proj_surjective := fun _ => projective_surjective
  normal_cover := fun N hN hNb => ⟨(), normal_cover N hN hNb⟩
  tailSlope := 3 / 4
  tailConstant := 2 * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4))
  tailConstant_nonneg := by positivity
  tail := fun b J => by
    have hlift := epi_card_le_centralLift (J := J) projective projective_surjective
      central_of_ker
    have hS4 := NaturalS4.epi_card_le J
    have hhom := binaryTargetOrder_hom_card_le_of_card_pow_two (J := J) 1
      card_ker_projective
    have hrank : binaryCharacterRank J ≤ b / 2 := by
      have := permutation_binaryCharacterRank_le_half J (Fin b)
      rw [Nat.card_fin] at this
      exact this
    have hhom' : (Nat.card (J →* projective.ker) : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * b) := by
      calc (Nat.card (J →* projective.ker) : ℝ) ≤ ((2 ^ (b / 2) : ℕ) : ℝ) := by
            exact_mod_cast hhom.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ ≤ (2 : ℝ) ^ ((Real.logb 2 2 / 2) * b) := by
            push_cast
            exact DerivedHead.pow_floor_div_le_rpow 2 b (by norm_num)
        _ = (2 : ℝ) ^ ((1 / 2 : ℝ) * b) := by rw [Real.logb_self_eq_one (by norm_num)]
    calc (Nat.card (GroupEpimorphism J GL3) : ℝ)
        ≤ (Nat.card (GroupEpimorphism J (Perm (Fin 4))) : ℝ) *
            (Nat.card (J →* projective.ker) : ℝ) := by exact_mod_cast hlift
      _ ≤ ((2 * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4)) : ℝ) * (2 : ℝ) ^ ((1 / 4 : ℝ) * b)) *
            (2 : ℝ) ^ ((1 / 2 : ℝ) * b) :=
          mul_le_mul hS4 hhom' (Nat.cast_nonneg _) (by positivity)
      _ = 2 * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4)) * (2 : ℝ) ^ ((3 / 4 : ℝ) * b) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num)]
          ring_nf
  comparator_window := by
    have hw := lin_width e
    subst hw
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := by
    have hw := lin_width e
    subst hw
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

/-- The SL mode: comparator `A₄ × C₂` on `4 + 2` points through `A₄`. -/
def linSLModel {w : ℕ} (i : PreE7NonPairActionClass w) (e : NV ≃ Fin w)
    (h : preE7NonPairAction w i = relabelSubgroup e (natural.comp slSub.subtype).range) :
    PreE7FactorComparatorModel w i where
  G := SL3
  equiv := relabelModelEquiv (natural.comp slSub.subtype)
    (natural_injective.comp Subtype.val_injective) e h
  P := NaturalS4.a4
  π := projectiveSL
  π_surjective := projectiveSL_surjective
  normal_cover := normal_cover_SL
  R := NaturalS4.a4 × Multiplicative (ZMod 2)
  degree := 4 + (1 + 1)
  action := a4c2Action
  action_injective := a4c2Action_injective
  σ := MonoidHom.fst _ _
  σ_surjective := Prod.fst_surjective
  tailSlope := 0
  mainConstant := 1
  tailConstant := 0
  mainConstant_nonneg := zero_le_one
  tailConstant_nonneg := le_rfl
  bottom := fun _ J => slBottom_le J
  comparator_window := by
    have hw := lin_width e
    subst hw
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := by
    have hw := lin_width e
    subst hw
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

/-- **LIN.**  Both actual linear actions are accepted by the mixed local
catalogue. -/
theorem preE7_lin_localFamilyAction (w : ℕ) (i : PreE7NonPairActionClass w)
    (S : PreE7LinSource w i) : preE7NoPairNoC3EarlierLocalFamilyAction .lin w i := by
  cases S with
  | gl e h => exact (linGLModel i e h).localFamilyAction .lin
  | sl e h => exact (linSLModel i e h).localFamilyAction .lin

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
