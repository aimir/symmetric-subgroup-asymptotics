import SymmetricSubgroupAsymptotics.CentralExtensionSemidirectStabilizer
import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusFirstLayer

/-! The two characteristic layers of the literal rank-two unitary
radical, with the actual quadratic-field torus action. The quotient
coordinate is entry(1,2), whose weight is sigma(t^2/sigma(t)). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryNaturalRadical

private def centerAutHom {N : Type*} [Group N] :
    MulAut N →* MulAut (Subgroup.center N) where
  toFun f := Subgroup.centerCongr f
  map_one' := by apply MulEquiv.ext; intro z; apply Subtype.ext; rfl
  map_mul' f g := by apply MulEquiv.ext; intro z; apply Subtype.ext; rfl

def rankTwoCentralEquiv (q : CFSG.PrimePower) :
    Multiplicative (centralParameters q 0) ≃* Subgroup.center (fixedRadical q 0) :=
  (MonoidHom.ofInjective (centralRadicalHom_injective q 0)).trans
    (MulEquiv.subgroupCongr ((centralRadicalHom_range_eq_kernel q 0).trans
      (fixedRadical_center_eq_kernel q 0).symm))

theorem rankTwoCentralEquiv_val (q : CFSG.PrimePower)
    (c : Multiplicative (centralParameters q 0)) :
    (rankTwoCentralEquiv q c).val = centralRadicalHom q 0 c := rfl

def rankTwoCentralTorusAutHom (q : CFSG.PrimePower) :
    (q.Extension 2)ˣ →* MulAut (Multiplicative (centralParameters q 0)) :=
  (MulAut.congr (rankTwoCentralEquiv q).symm).toMonoidHom.comp
    (centerAutHom.comp (rankTwoRadicalTorusAutHom q))

theorem rankTwoCentralTorus_intertwine (q : CFSG.PrimePower)
    (z : (q.Extension 2)ˣ) (c : Multiplicative (centralParameters q 0)) :
    rankTwoRadicalTorusAutHom q z (centralRadicalHom q 0 c) =
      centralRadicalHom q 0 (rankTwoCentralTorusAutHom q z c) := by
  have he := congrArg (fun a : Subgroup.center (fixedRadical q 0) => a.val)
    ((rankTwoCentralEquiv q).apply_symm_apply
      (Subgroup.centerCongr (rankTwoRadicalTorusAutHom q z) (rankTwoCentralEquiv q c)))
  exact he.symm

theorem rankTwoCentralTorus_scalar (q : CFSG.PrimePower)
    (z : (q.Extension 2)ˣ) (c : Multiplicative (centralParameters q 0)) :
    (rankTwoCentralTorusAutHom q z c).toAdd.val =
      (z : q.Extension 2) * definingFieldAutomorphism q 2 z * c.toAdd.val := by
  let d : Multiplicative (centralParameters q 0) := Multiplicative.ofAdd
    ⟨(z : q.Extension 2) * definingFieldAutomorphism q 2 z * c.toAdd.val,
      (centralCondition_iff q 0 _).mp
        (centralParameter_norm_mul_condition q 0 z c.toAdd.val
          (centralParameters_condition q 0 c.toAdd.val c.toAdd.property))⟩
  have hφ : rankTwoRadicalTorusAutHom q z (centralRadicalHom q 0 c) =
      centralRadicalHom q 0 d := by
    apply Subtype.ext
    change rankTwoNaturalTorus q z * centralFixed q 0 c.toAdd.val
        (centralParameters_condition q 0 c.toAdd.val c.toAdd.property) *
          (rankTwoNaturalTorus q z)⁻¹ =
      centralFixed q 0 d.toAdd.val
        (centralParameters_condition q 0 d.toAdd.val d.toAdd.property)
    exact rankTwoNaturalTorus_centralFixed_conjugation q z c.toAdd.val
      (centralParameters_condition q 0 c.toAdd.val c.toAdd.property)
  have hd := centralRadicalHom_injective q 0
    ((rankTwoCentralTorus_intertwine q z c).symm.trans hφ)
  exact congrArg (fun a : Multiplicative (centralParameters q 0) => a.toAdd.val) hd

private def additiveAutToMultiplicative {A : Type*} [AddGroup A]
    (f : AddAut A) : MulAut (Multiplicative A) where
  toFun x := Multiplicative.ofAdd (f x.toAdd)
  invFun x := Multiplicative.ofAdd (f.symm x.toAdd)
  left_inv x := f.symm_apply_apply x.toAdd
  right_inv x := f.apply_symm_apply x.toAdd
  map_mul' x y := map_add f x.toAdd y.toAdd

private def additiveAutToMultiplicativeHom {A : Type*} [AddGroup A] :
    AddAut A →* MulAut (Multiplicative A) where
  toFun := additiveAutToMultiplicative
  map_one' := by apply MulEquiv.ext; intro x; rfl
  map_mul' f g := by apply MulEquiv.ext; intro x; rfl

def rankTwoQuotientTorusAutHom (q : CFSG.PrimePower) :
    (q.Extension 2)ˣ →* MulAut (Multiplicative (q.Extension 2)) :=
  additiveAutToMultiplicativeHom.comp
    ((rankTwoFirstLayerAutHom q).comp (rankTwoRadicalTorusAutHom q))

theorem rankTwoQuotientTorus_intertwine (q : CFSG.PrimePower)
    (z : (q.Extension 2)ˣ) (g : fixedRadical q 0) :
    rankTwoParameterHom q (rankTwoRadicalTorusAutHom q z g) =
      rankTwoQuotientTorusAutHom q z (rankTwoParameterHom q g) := by
  apply Multiplicative.toAdd.injective
  exact (rankTwoFirstLayerAutHom_first q (rankTwoRadicalTorusAutHom q z) g).symm

theorem rankTwoQuotientTorus_scalar (q : CFSG.PrimePower)
    (z : (q.Extension 2)ˣ) (v : Multiplicative (q.Extension 2)) :
    (rankTwoQuotientTorusAutHom q z v).toAdd =
      definingFieldAutomorphism q 2
        (CFSGTwistedA2DiagonalTorus.firstWeight (q.Extension 2)
          (definingFieldAutomorphism q 2) (z : q.Extension 2)) * v.toAdd := by
  change rankTwoFirstLayerAutHom q (rankTwoRadicalTorusAutHom q z) v.toAdd = _
  rw [rankTwoFirstLayer_torus]
  change (rankTwoFirstWeightHom q (rankTwoSigmaUnits q z) : q.Extension 2) * v.toAdd = _
  rw [rankTwoFirstWeight_sigma]

theorem rankTwo_semidirect_index_mul_layer_cards (q : CFSG.PrimePower)
    (M : Subgroup (fixedRadical q 0 ⋊[rankTwoRadicalTorusAutHom q] (q.Extension 2)ˣ)) :
    M.index * Nat.card ((M.comap SemidirectProduct.inl).comap (centralRadicalHom q 0)) *
        Nat.card ((M.comap SemidirectProduct.inl).map (rankTwoParameterHom q)) =
      q.order ^ 3 * (M.map SemidirectProduct.rightHom).index := by
  have hexact : (centralRadicalHom q 0).range = (rankTwoParameterHom q).ker := by
    rw [rankTwoParameterHom_ker, centralRadicalHom_range_eq_kernel]
  have h := CentralExtensionSemidirectStabilizer.index_mul_layer_cards
    (rankTwoRadicalTorusAutHom q) (rankTwoParameterHom q)
    (rankTwoParameterHom_surjective q) (centralRadicalHom q 0) hexact M
  have hZ : Nat.card (Multiplicative (centralParameters q 0)) = q.order :=
    (Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (centralParameters q 0) ≃ centralParameters q 0)).trans
        (centralParameters_card q 0)
  have hV : Nat.card (Multiplicative (q.Extension 2)) = q.order ^ 2 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (q.Extension 2) ≃ q.Extension 2)).trans
      (extension_two_card q)
  rw [hZ, hV] at h
  calc
    _ = q.order * q.order ^ 2 * (M.map SemidirectProduct.rightHom).index := h
    _ = _ := by ring

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
