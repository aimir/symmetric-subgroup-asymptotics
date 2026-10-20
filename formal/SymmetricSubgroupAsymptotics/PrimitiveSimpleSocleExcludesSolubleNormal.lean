import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.AffineCoprimeCyclicSocles

/-! Actual one-factor nonabelian socles cannot coexist with an actual
nontrivial soluble normal subgroup. In particular an actual affine-model
isomorphism excludes this branch, without an action-order classification. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.oneFactor_no_nontrivial_soluble_normal
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (K : Subgroup G) [K.Normal] [IsSolvable K] (hK : K≠⊥) : False := by
  have hle := D.oneFactor_socle_le hk K inferInstance hK
  letI : IsSolvable (finiteGroupSocle G) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  have hs : IsSolvable D.Simple := solvable_of_surjective
    (f := (D.oneFactorEquiv hk).toMonoidHom) (D.oneFactorEquiv hk).surjective
  exact D.noncommutative (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))

/-- An actual affine group model supplies its own nontrivial soluble
normal translation subgroup. No irreducibility premise is needed here. -/
theorem NonaffineData.oneFactor_not_affineModel
    (D : NonaffineData G X) (hk : D.factorCount=1)
    {p d : ℕ} [Fact p.Prime] (hd : 0<d)
    (R : Subgroup (AffineModel.GLV p d)) (e : G≃*AffineModel.Aff R) : False := by
  let V := AffineModel.Vsub R
  let K := V.comap e.toMonoidHom
  let eK : K≃*V :=
    { toFun := fun g => ⟨e g.val,g.property⟩
      invFun := fun v => ⟨e.symm v.val,by
        change e (e.symm v.val)∈V
        simpa only [e.apply_symm_apply] using v.property⟩
      left_inv := fun g => Subtype.ext (e.symm_apply_apply g.val)
      right_inv := fun v => Subtype.ext (e.apply_symm_apply v.val)
      map_mul' := fun g h => Subtype.ext (e.map_mul g.val h.val) }
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  letI : Nontrivial V := (AffineModel.translationEquiv R).symm.injective.nontrivial
  letI : Nontrivial K := eK.symm.injective.nontrivial
  letI : IsSolvable V := solvable_of_solvable_injective
    (f := (AffineModel.translationEquiv R).toMonoidHom)
    (AffineModel.translationEquiv R).injective
  letI : IsSolvable K := solvable_of_solvable_injective (f := eK.toMonoidHom) eK.injective
  exact D.oneFactor_no_nontrivial_soluble_normal hk K (K.nontrivial_iff_ne_bot.mp inferInstance)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
