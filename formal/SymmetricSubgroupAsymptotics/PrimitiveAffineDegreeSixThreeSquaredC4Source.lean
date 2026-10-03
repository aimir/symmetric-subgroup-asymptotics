import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixNormalComparatorSource
import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel

/-!
# The degree-six `3² : C₄` affine cell

The irreducible order-four complement acts on `F₃²`.  The resulting
affine group has its translation subgroup in every nontrivial normal subgroup,
so every nonbottom quotient is a quotient of `C₄`, in its faithful regular
degree-four action.  The bottom quotient is the standard affine ternary
cyclic-dual target.

The recognition structure retains the literal irreducible complement inside
`GL₂(3)`.  A block-cell classifier can therefore construct this source
without choosing an unrelated abstract group of order thirty-six.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace DegreeSixThreeSquaredC4

abbrev C4 := Multiplicative (ZMod 4)

/-- The regular four-point chart of `C₄`. -/
def pointEquiv : C4 ≃ Fin 4 :=
  Multiplicative.toAdd.trans (ZMod.finEquiv 4).symm.toEquiv

def action : C4 →* Equiv.Perm (Fin 4) :=
  pointEquiv.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom C4 C4)

theorem action_injective : Function.Injective action :=
  pointEquiv.permCongrHom.injective.comp MulAction.toPerm_injective

end DegreeSixThreeSquaredC4

namespace Non2UnipotentPrefixFiniteMenu

/-- Recognition of the irreducible `3² : C₄` model. -/
structure PreE7DegreeSixThreeSquaredC4Source
    (U : PreE7NonPairActionClass 6) : Type where
  R : Subgroup (AffineModel.GLV 3 2)
  irreducible : AffineModel.Irreducible R
  topEquiv : R ≃* DegreeSixThreeSquaredC4.C4
  equiv : preE7NonPairAction 6 U ≃* AffineModel.Aff R

namespace PreE7DegreeSixThreeSquaredC4Source

variable {U : PreE7NonPairActionClass 6}
  (S : PreE7DegreeSixThreeSquaredC4Source U)

/-- The nontrivial abelian complement has derived length one. -/
def length : AffineModel.DerivedLength S.R := by
  letI : Nontrivial DegreeSixThreeSquaredC4.C4 :=
    ⟨⟨Multiplicative.ofAdd (0 : ZMod 4),
      Multiplicative.ofAdd (1 : ZMod 4), by
      intro h
      have := congrArg Multiplicative.toAdd h
      exact (by decide : (0 : ZMod 4) ≠ 1) this⟩⟩
  letI : Nontrivial S.R := S.topEquiv.toEquiv.nontrivial
  refine
    { t := 0
      top_eq := ?_
      prev_ne := ?_ }
  · rw [Nat.zero_add, derivedSeries_one]
    apply (commutator_eq_bot_iff S.R).mpr
    apply isMulCommutative_iff.mpr
    intro x y
    apply S.topEquiv.injective
    simpa using mul_comm (S.topEquiv x) (S.topEquiv y)
  · rw [derivedSeries_zero]
    exact top_ne_bot

/-- Quotient by the translations, with its literal `C₄` chart. -/
def topProjection : AffineModel.Aff S.R →* DegreeSixThreeSquaredC4.C4 :=
  S.topEquiv.toMonoidHom.comp SemidirectProduct.rightHom

theorem topProjection_surjective : Function.Surjective S.topProjection :=
  S.topEquiv.surjective.comp SemidirectProduct.rightHom_surjective

theorem topProjection_ker_le_normal
    (N : Subgroup (AffineModel.Aff S.R)) (hN : N.Normal) (hNb : N ≠ ⊥) :
    S.topProjection.ker ≤ N := by
  haveI : N.Normal := hN
  have hV := AffineModel.Vsub_le_normal S.irreducible N hNb
  intro x hx
  apply hV
  rw [AffineModel.mem_Vsub]
  have htop : S.topEquiv x.right = 1 := by
    exact (MonoidHom.mem_ker.mp hx)
  exact S.topEquiv.injective (htop.trans (map_one S.topEquiv).symm)

/-- The completed normal-comparator model. -/
def model : PreE7NormalComparatorModel 6 U where
  G := AffineModel.Aff S.R
  equiv := S.equiv
  index := Unit
  R := DegreeSixThreeSquaredC4.C4
  degree := 4
  action := DegreeSixThreeSquaredC4.action
  action_injective := DegreeSixThreeSquaredC4.action_injective
  proj := fun _ => S.topProjection
  proj_surjective := fun _ => S.topProjection_surjective
  normal_cover := fun N hN hNb =>
    ⟨(), S.topProjection_ker_le_normal N hN hNb⟩
  tailSlope := Real.logb 2 3 / 3
  tailConstant := Nat.card
    (AffineModel.Aff S.R ≃* AffineModel.Aff S.R)
  tailConstant_nonneg := by positivity
  tail := fun _ J =>
    (AffineModel.target S.irreducible S.length (by norm_num)).epi_card_le_ternary J
  comparator_window := by
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := logThreeThird_le_window (by norm_num)

theorem model_card : Nat.card (AffineModel.Aff S.R) = 36 := by
  have hV : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
      Nat.card_zmod]
    norm_num
  rw [SemidirectProduct.card, hV, Nat.card_congr S.topEquiv.toEquiv]
  norm_num [DegreeSixThreeSquaredC4.C4]

theorem automorphism_card_le :
    Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) ≤ 2 ^ 216 := by
  calc
    Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) ≤
        Nat.card (AffineModel.Aff S.R) ^
          Nat.log 2 (Nat.card (AffineModel.Aff S.R)) :=
      mulEquiv_card_le_card_pow_log (AffineModel.Aff S.R)
    _ = 36 ^ 5 := by rw [S.model_card]; norm_num
    _ ≤ 2 ^ 216 := by norm_num

private theorem tailConstant_le :
    S.model.tailConstant ≤ (2 : ℝ) ^ (36 * (6 : ℝ)) := by
  change (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) ≤ _
  calc
    (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) ≤
        ((2 ^ 216 : ℕ) : ℝ) := by
      exact_mod_cast S.automorphism_card_le
    _ = (2 : ℝ) ^ (36 * (6 : ℝ)) := by norm_num

/-- Completed degree-six source for the irreducible `3² : C₄` cell. -/
noncomputable def source : PreE7RankTailSourceOrYonedaTopData 6 U :=
  DegreeSixNormalComparatorSource.source S.model S.tailConstant_le

end PreE7DegreeSixThreeSquaredC4Source
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
