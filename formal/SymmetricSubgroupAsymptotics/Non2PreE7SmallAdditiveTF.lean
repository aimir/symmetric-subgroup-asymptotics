import SymmetricSubgroupAsymptotics.Non2PreE7TwoFourDiagonalG
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveLin

/-!
# TF: the three named diagonal two-block classes (D0391)

The family is exactly the three named actual degree-eight classes
`Xc = ⟨V₄², a, s⟩`, `Xg = ⟨V₄², a, τ s⟩`, `Xs = ⟨V₄², a, τ, s⟩` with
`a = (123)(567)`, `τ = (12)(56)`, `s = (15)(26)(37)(48)`, up to relabeling.

* `Xc`: comparator `A₄ × C₂` on `4 + 2` points; common source `J'`.
* `Xs`: comparator `S₄ × C₂` on `4 + 2` points; common source `J''`.
* `Xg`: comparator `S₄` on four points, through each of the three
  projections with kernels the three minimal normal subgroups; common
  source `J''`.

In each case every nontrivial literal quotient is a quotient of the
comparator, and `|Epi(J, X)| ≤ |Aut X| · 2^(b/2)`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace LinearThree

open Equiv

/-- `S₄ × C₂` on `4 + 2` points. -/
def s4c2Action : Perm (Fin 4) × Multiplicative (ZMod 2) →* Perm (Fin (4 + (1 + 1))) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 4)) finSumFinEquiv).trans finSumFinEquiv).permCongrHom.toMonoidHom.comp
    ((Perm.sumCongrHom (Fin 4) (Fin 1 ⊕ Fin 1)).comp
      ((MonoidHom.id _).prodMap (C2Wreath.blockSwap (Fin 1))))

theorem s4c2Action_injective : Function.Injective s4c2Action := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : (Perm.sumCongrHom (Fin 4) (Fin 1 ⊕ Fin 1))
      (((MonoidHom.id _).prodMap (C2Wreath.blockSwap (Fin 1))) x) = 1 := by
    apply (((Equiv.sumCongr (Equiv.refl (Fin 4)) finSumFinEquiv).trans
      finSumFinEquiv).permCongrHom).injective
    rw [map_one]
    exact hx
  have h2 := Perm.sumCongrHom_injective (h1.trans (map_one _).symm)
  have ha : x.1 = 1 := congrArg Prod.fst h2
  have hb : C2Wreath.blockSwap (Fin 1) x.2 = 1 := congrArg Prod.snd h2
  refine Prod.ext ha ?_
  rcases C2Wreath.cases x.2 with h | h
  · exact h
  · exfalso
    rw [h, C2Wreath.blockSwap] at hb
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, C2Wreath.gen_ne_one, if_false] at hb
    have := congrArg (fun σ : Perm (Fin 1 ⊕ Fin 1) => σ (Sum.inl 0)) hb
    simp at this

end LinearThree

namespace Non2UnipotentPrefixFiniteMenu

open Equiv TwoFourDiagonal LinearThree

/-- The image of a named class in the natural two-block action. -/
theorem closure_map_eq (X : Subgroup W4) (S : Set W4) (h : X = Subgroup.closure S) :
    (Subgroup.closure S).map TwoFourDiagonal.natural = (TwoFourDiagonal.natural.comp X.subtype).range := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, h]

/-- The TF family: one of the three named classes, up to relabeling. -/
structure PreE7TFSource (w : ℕ) (i : PreE7NonPairActionClass w) : Prop where
  named : ∃ e : Fin 4 ⊕ Fin 4 ≃ Fin w,
    preE7NonPairAction w i = relabelSubgroup e ((Subgroup.closure XcGens).map natural) ∨
    preE7NonPairAction w i = relabelSubgroup e ((Subgroup.closure XgGens).map natural) ∨
    preE7NonPairAction w i = relabelSubgroup e ((Subgroup.closure XsGens).map natural)

theorem tf_width {w : ℕ} (e : Fin 4 ⊕ Fin 4 ≃ Fin w) : w = 8 := by
  rw [width_eq_of_relabel e]
  simp

theorem natural_comp_injective (X : Subgroup W4) :
    Function.Injective (TwoFourDiagonal.natural.comp X.subtype) :=
  natural_injective.comp Subtype.val_injective

/-- `Xc`: comparator `A₄ × C₂`. -/
def tfXcModel {w : ℕ} (i : PreE7NonPairActionClass w) (e : Fin 4 ⊕ Fin 4 ≃ Fin w)
    (h : preE7NonPairAction w i = relabelSubgroup e ((Subgroup.closure XcGens).map natural)) :
    PreE7NormalComparatorModel w i where
  G := Xc
  equiv := relabelModelEquiv _ (natural_comp_injective Xc) e
    (h.trans (by rw [closure_map_eq Xc XcGens Xc_eq_closure]))
  index := Unit
  R := NaturalS4.a4 × Multiplicative (ZMod 2)
  degree := 4 + (1 + 1)
  action := a4c2Action
  action_injective := a4c2Action_injective
  proj := fun _ => projC
  proj_surjective := fun _ => projC_surjective
  normal_cover := fun N hN hNb => ⟨(), projC_normal_cover N hN hNb⟩
  tailSlope := 1 / 2
  tailConstant := Nat.card (Xc ≃* Xc)
  tailConstant_nonneg := by positivity
  tail := fun _ J => targetC.epi_card_le_binary J
  comparator_window := by
    have hw := tf_width e
    subst hw
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := by
    have hw := tf_width e
    subst hw
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

/-- `Xg`: comparator `S₄` through three projections. -/
def tfXgModel {w : ℕ} (i : PreE7NonPairActionClass w) (e : Fin 4 ⊕ Fin 4 ≃ Fin w)
    (h : preE7NonPairAction w i = relabelSubgroup e ((Subgroup.closure XgGens).map natural)) :
    PreE7NormalComparatorModel w i where
  G := Xg
  equiv := relabelModelEquiv _ (natural_comp_injective Xg) e
    (h.trans (by rw [closure_map_eq Xg XgGens Xg_eq_closure]))
  index := Fin 3
  R := Perm (Fin 4)
  degree := 4
  action := MonoidHom.id _
  action_injective := Function.injective_id
  proj := projG
  proj_surjective := projG_surjective
  normal_cover := projG_normal_cover
  tailSlope := 1 / 2
  tailConstant := Nat.card (Xg ≃* Xg)
  tailConstant_nonneg := by positivity
  tail := fun _ J => targetG.epi_card_le_binary J
  comparator_window := by
    have hw := tf_width e
    subst hw
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := by
    have hw := tf_width e
    subst hw
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

/-- `Xs`: comparator `S₄ × C₂`. -/
def tfXsModel {w : ℕ} (i : PreE7NonPairActionClass w) (e : Fin 4 ⊕ Fin 4 ≃ Fin w)
    (h : preE7NonPairAction w i = relabelSubgroup e ((Subgroup.closure XsGens).map natural)) :
    PreE7NormalComparatorModel w i where
  G := Xs
  equiv := relabelModelEquiv _ (natural_comp_injective Xs) e
    (h.trans (by rw [closure_map_eq Xs XsGens Xs_eq_closure]))
  index := Unit
  R := Perm (Fin 4) × Multiplicative (ZMod 2)
  degree := 4 + (1 + 1)
  action := s4c2Action
  action_injective := s4c2Action_injective
  proj := fun _ => projS
  proj_surjective := fun _ => projS_surjective
  normal_cover := fun N hN hNb => ⟨(), projS_normal_cover N hN hNb⟩
  tailSlope := 1 / 2
  tailConstant := Nat.card (Xs ≃* Xs)
  tailConstant_nonneg := by positivity
  tail := fun _ J => targetS.epi_card_le_binary J
  comparator_window := by
    have hw := tf_width e
    subst hw
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := by
    have hw := tf_width e
    subst hw
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

/-- **TF.**  The three named classes are accepted by the mixed local
catalogue. -/
theorem preE7_tf_localFamilyAction (w : ℕ) (i : PreE7NonPairActionClass w)
    (S : PreE7TFSource w i) : preE7NoPairNoC3EarlierLocalFamilyAction .tf w i := by
  obtain ⟨e, h | h | h⟩ := S.named
  · exact (tfXcModel i e h).localFamilyAction .tf
  · exact (tfXgModel i e h).localFamilyAction .tf
  · exact (tfXsModel i e h).localFamilyAction .tf

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
