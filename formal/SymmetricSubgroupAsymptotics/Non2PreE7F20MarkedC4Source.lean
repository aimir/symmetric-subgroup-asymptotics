import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.FusionCompleteQuotientTransfer

/-!
# F20: the natural degree-five Frobenius action and its complete source

The historical F20 owner (D0386) is the natural action of
`C5 ⋊ C4 = AGL₁(5)` on the five points of `F₅`.  This file defines the
actual action predicate and proves its complete per-source bound on the
literal normal axes of the original action:

`Z_J(U) = ∑_{N ⊴ U} |Epi(J, U/N)| ≤ |Epi(J, U)| + |Hom(J, C4)|`,

`|Epi(J, U)| ≤ |Aut(C5 ⋊ C4)| · 2^((log₂ 5 / 5) b)`.

The translations `C5` form a self-centralizing minimal normal subgroup, so
every nontrivial literal axis contains them, and every nonbottom literal
quotient is a quotient of the cyclic group `U / C5 ≅ C4`.  The quotients of a
cyclic group embed into it with pairwise distinct images, so the nonbottom
axes are paid together by the single correlated count `|Hom(J, C4)|` of the
same source `J`.  No independent per-axis worst case is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-! ## Quotients of a finite cyclic group -/

section CyclicMenu

variable {A : Type*} [CommGroup A] [Finite A] [IsCyclic A]

/-- In a finite cyclic group, `M` is the kernel of `a ↦ a ^ |M|`. -/
theorem cyclic_ker_powCard (M : Subgroup A) :
    (powMonoidHom (Nat.card M) : A →* A).ker = M := by
  letI := Fintype.ofFinite A
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have h := pow_card_eq_one' (G := M) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val h
  · have h := IsCyclic.card_pow_eq_one_le (α := A) (n := Nat.card M) Nat.card_pos
    calc Nat.card (powMonoidHom (Nat.card M) : A →* A).ker
        = Fintype.card {a : A // a ^ Nat.card M = 1} := by
          rw [← Nat.card_eq_fintype_card]
          rfl
      _ = (Finset.univ.filter (fun a : A => a ^ Nat.card M = 1)).card :=
          Fintype.card_subtype _
      _ ≤ Nat.card M := h

/-- Subgroups of a finite cyclic group are determined by their order. -/
theorem cyclic_subgroup_eq_of_card_eq {M M' : Subgroup A}
    (h : Nat.card M = Nat.card M') : M = M' := by
  rw [← cyclic_ker_powCard M, ← cyclic_ker_powCard M', h]

/-- The embedding of a quotient of a cyclic group into the group. -/
def cyclicQuotientEmbedding (M : Subgroup A) : A ⧸ M →* A :=
  (QuotientGroup.kerLift (powMonoidHom (Nat.card M) : A →* A)).comp
    (QuotientGroup.quotientMulEquivOfEq (cyclic_ker_powCard M).symm).toMonoidHom

theorem cyclicQuotientEmbedding_injective (M : Subgroup A) :
    Function.Injective (cyclicQuotientEmbedding M) := by
  intro x y h
  simp only [cyclicQuotientEmbedding, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom] at h
  exact (MulEquiv.injective _) (QuotientGroup.kerLift_injective _ h)

end CyclicMenu

/-! ## Literal normal menus through a cyclic quotient -/

section NormalMenu

variable {G A J : Type*} [Group G] [Finite G] [CommGroup A] [Finite A] [IsCyclic A]
  [Group J] [Finite J]

/-- The embedding of a nonbottom literal quotient into the cyclic quotient. -/
def cyclicAxisEmbedding (π : G →* A) (hπ : Function.Surjective π)
    (N : Subgroup G) [N.Normal] (hN : π.ker ≤ N) : G ⧸ N →* A :=
  (cyclicQuotientEmbedding (N.map π)).comp
    (quotientEquivOfKerLe π hπ N hN).toMonoidHom

omit [Finite G] in
theorem cyclicAxisEmbedding_injective (π : G →* A) (hπ : Function.Surjective π)
    (N : Subgroup G) [N.Normal] (hN : π.ker ≤ N) :
    Function.Injective (cyclicAxisEmbedding π hπ N hN) := by
  intro x y h
  simp only [cyclicAxisEmbedding, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom] at h
  exact (MulEquiv.injective _) (cyclicQuotientEmbedding_injective _ h)

omit [Finite G] in
/-- Two literal axes above the kernel with quotients of equal order coincide. -/
theorem axis_eq_of_card_quotient_eq (π : G →* A) (hπ : Function.Surjective π)
    (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal]
    (h₁ : π.ker ≤ N₁) (h₂ : π.ker ≤ N₂)
    (hcard : Nat.card (G ⧸ N₁) = Nat.card (G ⧸ N₂)) : N₁ = N₂ := by
  have e₁ := quotientEquivOfKerLe π hπ N₁ h₁
  have e₂ := quotientEquivOfKerLe π hπ N₂ h₂
  have hq : Nat.card (A ⧸ N₁.map π) = Nat.card (A ⧸ N₂.map π) := by
    rw [← Nat.card_congr e₁.toEquiv, ← Nat.card_congr e₂.toEquiv, hcard]
  have hA₁ := Subgroup.card_eq_card_quotient_mul_card_subgroup (N₁.map π)
  have hA₂ := Subgroup.card_eq_card_quotient_mul_card_subgroup (N₂.map π)
  have hpos : 0 < Nat.card (A ⧸ N₁.map π) := Nat.card_pos
  have hM : Nat.card (N₁.map π) = Nat.card (N₂.map π) := by
    have hmul : Nat.card (A ⧸ N₁.map π) * Nat.card (N₁.map π) =
        Nat.card (A ⧸ N₁.map π) * Nat.card (N₂.map π) := by
      rw [← hA₁, hq, ← hA₂]
    exact Nat.eq_of_mul_eq_mul_left hpos hmul
  have hmap := cyclic_subgroup_eq_of_card_eq hM
  calc N₁ = (N₁.map π).comap π := by
        rw [Subgroup.comap_map_eq, sup_eq_left.mpr h₁]
    _ = (N₂.map π).comap π := by rw [hmap]
    _ = N₂ := by rw [Subgroup.comap_map_eq, sup_eq_left.mpr h₂]

/-- **The cyclic menu.**  If every nontrivial literal normal subgroup contains
the kernel of an onto map to a cyclic group `A`, then the complete literal
quotient sum is at most the onto count of `G` plus `|Hom(J, A)|`. -/
theorem normalMenu_epi_sum_le_cyclic (π : G →* A) (hπ : Function.Surjective π)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → π.ker ≤ N) :
    (∑ N : {N : Subgroup G // N.Normal}, Nat.card (GroupEpimorphism J (G ⧸ N.1))) ≤
      Nat.card (GroupEpimorphism J G) + Nat.card (J →* A) := by
  letI : Finite (J →* A) := Finite.of_injective (fun f : J →* A => (f : J → A))
    DFunLike.coe_injective
  let bot : {N : Subgroup G // N.Normal} := ⟨⊥, Subgroup.normal_bot⟩
  let f : {N : Subgroup G // N.Normal} → ℕ := fun N =>
    Nat.card (GroupEpimorphism J (G ⧸ N.1))
  have hsplit : (∑ N : {N : Subgroup G // N.Normal}, f N) =
      f bot + ∑ N ∈ Finset.univ.erase bot, f N :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ bot)).symm
  have hbot : f bot = Nat.card (GroupEpimorphism J G) :=
    fusionGroupEpimorphism_card_congr (MulEquiv.refl J) QuotientGroup.quotientBot
  -- the nonbottom axes inject jointly into `Hom(J, A)`
  let Ax := {N : {N : Subgroup G // N.Normal} // N ≠ bot}
  have hker : ∀ N : Ax, π.ker ≤ N.1.1 := by
    intro N
    apply hcover N.1.1 N.1.2
    intro h
    apply N.2
    exact Subtype.ext h
  let ι : ∀ N : Ax, G ⧸ N.1.1 →* A := fun N =>
    haveI : N.1.1.Normal := N.1.2
    cyclicAxisEmbedding π hπ N.1.1 (hker N)
  have hι : ∀ N : Ax, Function.Injective (ι N) := fun N =>
    haveI : N.1.1.Normal := N.1.2
    cyclicAxisEmbedding_injective π hπ N.1.1 (hker N)
  let F : (Σ N : Ax, GroupEpimorphism J (G ⧸ N.1.1)) → (J →* A) :=
    fun p => (ι p.1).comp p.2.1
  have hrange : ∀ p : (Σ N : Ax, GroupEpimorphism J (G ⧸ N.1.1)),
      Nat.card (F p).range = Nat.card (G ⧸ p.1.1.1) := by
    intro p
    have : (F p).range = (ι p.1).range := by
      change ((ι p.1).comp p.2.1).range = _
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ p.2.2,
        ← MonoidHom.range_eq_map]
    rw [this, Nat.card_congr (MonoidHom.ofInjective (hι p.1)).toEquiv.symm]
  have hF : Function.Injective F := by
    rintro ⟨N₁, f₁⟩ ⟨N₂, f₂⟩ h
    have hc : Nat.card (G ⧸ N₁.1.1) = Nat.card (G ⧸ N₂.1.1) := by
      rw [← hrange ⟨N₁, f₁⟩, ← hrange ⟨N₂, f₂⟩, h]
    have hN : N₁ = N₂ := by
      haveI : N₁.1.1.Normal := N₁.1.2
      haveI : N₂.1.1.Normal := N₂.1.2
      exact Subtype.ext (Subtype.ext (axis_eq_of_card_quotient_eq π hπ _ _
        (hker N₁) (hker N₂) hc))
    subst hN
    have hf : f₁ = f₂ := by
      apply Subtype.ext
      ext x
      exact hι N₁ (DFunLike.congr_fun h x)
    rw [hf]
  have hAx : (∑ N ∈ Finset.univ.erase bot, f N) =
      Nat.card (Σ N : Ax, GroupEpimorphism J (G ⧸ N.1.1)) := by
    rw [Finset.sum_subtype (Finset.univ.erase bot)
      (p := fun N => N ≠ bot) (fun N => by simp) f, Nat.card_sigma]
  have hle : Nat.card (Σ N : Ax, GroupEpimorphism J (G ⧸ N.1.1)) ≤
      Nat.card (J →* A) := Nat.card_le_card_of_injective F hF
  change (∑ N : {N : Subgroup G // N.Normal}, f N) ≤ _
  rw [hsplit, hbot, hAx]
  exact Nat.add_le_add_left hle _

end NormalMenu

/-! ## The natural `C5 ⋊ C4` model -/

namespace F20

open AffineModel

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The scalar chart of the one-dimensional linear group over `F₅`. -/
def scalar : (ZMod 5)ˣ →* GLV 5 1 := DistribMulAction.toModuleAut (ZMod 5) (V 5 1)

theorem scalar_apply (u : (ZMod 5)ˣ) (v : V 5 1) : scalar u v = (u : ZMod 5) • v := rfl

/-- The basis vector of `F₅¹`. -/
def e0 : V 5 1 := fun _ => 1

theorem eq_smul_e0 (v : V 5 1) : v = v 0 • e0 := by
  funext j
  fin_cases j
  simp [e0]

theorem scalar_bijective : Function.Bijective scalar := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro u hu
    have h := congrArg (fun f : GLV 5 1 => f e0 0) hu
    simp only [scalar_apply, e0, Pi.smul_apply, smul_eq_mul, mul_one] at h
    exact Units.ext h
  · intro f
    have hne : f e0 0 ≠ 0 := by
      intro h0
      have hf0 : f e0 = 0 := by
        funext j
        fin_cases j
        exact h0
      have : e0 = 0 := f.injective (hf0.trans (map_zero f).symm)
      have h1 := congrFun this 0
      simp [e0] at h1
    refine ⟨Units.mk0 _ hne, ?_⟩
    apply LinearEquiv.ext
    intro v
    rw [scalar_apply, Units.val_mk0]
    set c : ZMod 5 := f e0 0 with hc
    have hv : f v = v 0 • f e0 := by
      conv_lhs => rw [eq_smul_e0 v]
      exact map_smul f _ _
    have he : f e0 = c • e0 := eq_smul_e0 (f e0)
    rw [hv, he, smul_smul]
    conv_lhs => rw [eq_smul_e0 v]
    rw [smul_smul, mul_comm]

/-- `GL₁(F₅) ≅ F₅ˣ`. -/
def scalarEquiv : (ZMod 5)ˣ ≃* GLV 5 1 := MulEquiv.ofBijective scalar scalar_bijective

theorem card_units : Nat.card (ZMod 5)ˣ = 4 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units 5]

theorem card_GLV : Nat.card (GLV 5 1) = 4 := by
  rw [← Nat.card_congr scalarEquiv.toEquiv, card_units]

theorem GLV_comm (f g : GLV 5 1) : f * g = g * f := by
  obtain ⟨u, rfl⟩ := scalarEquiv.surjective f
  obtain ⟨v, rfl⟩ := scalarEquiv.surjective g
  rw [← map_mul, ← map_mul, mul_comm]

instance : IsCyclic (Multiplicative (ZMod 4)) := isCyclic_multiplicative

/-- `GL₁(F₅) ≅ C4`. -/
def c4Equiv : GLV 5 1 ≃* Multiplicative (ZMod 4) :=
  scalarEquiv.symm.trans (mulEquivOfCyclicCardEq (by
    rw [card_units, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]))

/-- The full linear group, as the complement of the natural Frobenius
group. -/
abbrev R : Subgroup (GLV 5 1) := ⊤

/-- `C5 ⋊ C4 = AGL₁(5)`. -/
abbrev G := Aff R

theorem card_V : Nat.card (V 5 1) = 5 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem card_G : Nat.card G = 20 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd, card_V, Subgroup.card_top, card_GLV]

theorem irreducible : AffineModel.Irreducible R := by
  intro S _
  haveI : Fact (Nat.card (V 5 1)).Prime := by
    rw [card_V]
    exact fact_prime_five
  exact AddSubgroup.eq_bot_or_eq_top_of_prime_card S

instance solvable : IsSolvable R :=
  isSolvable_of_comm (fun a b => Subtype.ext (GLV_comm a b))

theorem R_ne_bot : R ≠ ⊥ := by
  intro h
  have h1 : Nat.card R = 1 := by
    rw [h]
    exact Subgroup.card_bot
  rw [Subgroup.card_top, card_GLV] at h1
  norm_num at h1

/-- A fixed derived-length datum. -/
def derivedLength : DerivedLength R :=
  Classical.choice (derivedLength_nonempty R R_ne_bot)

/-- `C5 ⋊ C4` is a cyclic-dual target over `F₅` on `J^(t+1)`. -/
def target : DerivedHead.DerivedCyclicTarget G (Vsub R) derivedLength.t 5 :=
  AffineModel.target irreducible derivedLength (by norm_num)

/-- The onto count of the Frobenius group. -/
theorem epi_card_le {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J G) : ℝ) ≤
      (Nat.card (G ≃* G) : ℝ) * (2 : ℝ) ^ ((Real.logb 2 5 / 5) * b) := by
  have := target.epi_card_le_prime J
  simpa using this

/-- The quotient by the translations, charted as `C4`. -/
def topC4 : G →* Multiplicative (ZMod 4) :=
  c4Equiv.toMonoidHom.comp ((Subgroup.topEquiv).toMonoidHom.comp
    (SemidirectProduct.rightHom : G →* R))

theorem topC4_surjective : Function.Surjective topC4 := by
  intro c
  obtain ⟨g, rfl⟩ := c4Equiv.surjective c
  exact ⟨SemidirectProduct.inr ⟨g, Subgroup.mem_top g⟩, rfl⟩

theorem topC4_ker : topC4.ker = Vsub R := by
  ext y
  rw [MonoidHom.mem_ker, mem_Vsub]
  simp only [topC4, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.map_eq_one_iff, SemidirectProduct.rightHom_eq_right]

/-- Every nontrivial normal subgroup contains the translations. -/
theorem topC4_cover (N : Subgroup G) (hN : N.Normal) (hne : N ≠ ⊥) : topC4.ker ≤ N := by
  haveI := hN
  rw [topC4_ker]
  exact le_of_minimal_selfCentralizing (Vsub R) (minimal irreducible) (selfCentralizing R)
    N hne

theorem aut_card_le : Nat.card (G ≃* G) ≤ 160000 := by
  have h := Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log G
  rw [card_G] at h
  have hlog : Nat.log 2 20 = 4 := by
    rw [Nat.log_eq_iff (by norm_num)]
    norm_num
  rw [hlog] at h
  norm_num at h
  exact h

end F20

/-! ## The actual action predicate -/

namespace Non2UnipotentPrefixFiniteMenu

/-- **F20.**  The original action is literally a relabeling of the natural
degree-five action of `C5 ⋊ C4 = AGL₁(5)` on `F₅`. -/
structure PreE7F20Source (w : ℕ) (i : PreE7NonPairActionClass w) : Prop where
  natural : ∃ e : AffineModel.V 5 1 ≃ Fin w,
    preE7NonPairAction w i = relabelSubgroup e (AffineModel.action F20.R).range

namespace PreE7F20Source

variable {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7F20Source w i)

include S in
theorem width_eq : w = 5 := by
  obtain ⟨e, _⟩ := S.natural
  rw [width_eq_of_relabel e, F20.card_V]

/-- The original action is the Frobenius model group. -/
def equiv : preE7NonPairAction w i ≃* F20.G :=
  relabelModelEquiv _ (AffineModel.action_injective F20.R) (Classical.choose S.natural)
    (Classical.choose_spec S.natural)

/-- The original quotient by the translations, as `C4`. -/
def topC4 : preE7NonPairAction w i →* Multiplicative (ZMod 4) :=
  F20.topC4.comp S.equiv.toMonoidHom

theorem topC4_surjective : Function.Surjective S.topC4 :=
  F20.topC4_surjective.comp S.equiv.surjective

/-- Every nontrivial literal normal axis of the original action contains the
translations. -/
theorem topC4_cover (N : Subgroup (preE7NonPairAction w i)) (hN : N.Normal)
    (hne : N ≠ ⊥) : S.topC4.ker ≤ N := by
  let N' : Subgroup F20.G := N.map S.equiv.toMonoidHom
  have hN' : N'.Normal := hN.map _ S.equiv.surjective
  have hne' : N' ≠ ⊥ := by
    intro hb
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : S.equiv x ∈ N' := ⟨x, hx, rfl⟩
    rw [hb] at this
    have h1 : S.equiv x = 1 := (Subgroup.mem_bot).mp this
    exact (Subgroup.mem_bot).mpr (S.equiv.injective (h1.trans (map_one _).symm))
  intro x hx
  have hx' : S.equiv x ∈ F20.topC4.ker := hx
  obtain ⟨y, hy, hyx⟩ := F20.topC4_cover N' hN' hne' hx'
  have : y = x := S.equiv.injective hyx
  rw [← this]
  exact hy

include S

/-- The literal complete quotient sum of the original action is paid by its
onto count and the correlated `C4` character count of the same source. -/
theorem completeQuotient_le {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
        Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1))) ≤
      Nat.card (GroupEpimorphism J (preE7NonPairAction w i)) +
        Nat.card (J →* Multiplicative (ZMod 4)) :=
  normalMenu_epi_sum_le_cyclic S.topC4 S.topC4_surjective S.topC4_cover

/-- The onto count of the original action. -/
theorem epi_card_le {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (preE7NonPairAction w i)) : ℝ) ≤
      (Nat.card (F20.G ≃* F20.G) : ℝ) * (2 : ℝ) ^ ((Real.logb 2 5 / 5) * b) := by
  rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) S.equiv]
  exact F20.epi_card_le J

/-- **Complete per-source bound** on the literal normal axes, retaining every
accepted continuation: the surviving complete source is at most the onto
count plus the `C4` character count of the same `J`. -/
theorem completeSource_le {b : ℕ}
    (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
      (Nat.card (GroupEpimorphism J (preE7NonPairAction w i)) : ℝ) +
        Nat.card (J →* Multiplicative (ZMod 4)) := by
  have hsurv : ∀ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
      fusionSurvivingEpiCount (preE7NonPairAction w i) P N J ≤
        (Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) : ℝ) := by
    intro N
    unfold fusionSurvivingEpiCount
    exact_mod_cast Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  calc fusionCompleteSourceSum (preE7NonPairAction w i) P J
      ≤ ∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
          (Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) : ℝ) :=
        Finset.sum_le_sum (fun N _ => hsurv N)
    _ ≤ _ := by exact_mod_cast S.completeQuotient_le J

end PreE7F20Source

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
