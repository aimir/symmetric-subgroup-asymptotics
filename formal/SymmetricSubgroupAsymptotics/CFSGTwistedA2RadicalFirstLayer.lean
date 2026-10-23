import SymmetricSubgroupAsymptotics.CFSGCentralQuotientAutomorphism
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalCenter

/-! The intrinsic centre quotient of the SAME rank-two radical is the
additive quadratic extension, with literal coordinate intertwining for
every actual radical automorphism. No simplicity or torus premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

def rankTwoParameterHom (q : CFSG.PrimePower) :
    fixedRadical q 0 →* Multiplicative (q.Extension 2) where
  toFun g := Multiplicative.ofAdd ((fixedRadicalParameterHom q 0 g).toAdd 0)
  map_one' := by
    change Multiplicative.ofAdd ((fixedRadicalParameterHom q 0 1).toAdd 0) = 1
    rw [map_one]
    rfl
  map_mul' g h := by
    change Multiplicative.ofAdd ((fixedRadicalParameterHom q 0 (g * h)).toAdd 0) =
      Multiplicative.ofAdd ((fixedRadicalParameterHom q 0 g).toAdd 0) *
      Multiplicative.ofAdd ((fixedRadicalParameterHom q 0 h).toAdd 0)
    rw [map_mul]
    rfl

theorem rankTwoParameterHom_surjective (q : CFSG.PrimePower) :
    Function.Surjective (rankTwoParameterHom q) := by
  intro v
  obtain ⟨g, hg⟩ := fixedRadicalParameterHom_surjective q 0
    (Multiplicative.ofAdd (fun _ : Fin 1 => v.toAdd))
  refine ⟨g, ?_⟩
  change Multiplicative.ofAdd ((fixedRadicalParameterHom q 0 g).toAdd 0) = v
  rw [hg]
  exact ofAdd_toAdd v

theorem rankTwoParameterHom_ker (q : CFSG.PrimePower) :
    (rankTwoParameterHom q).ker = (fixedRadicalParameterHom q 0).ker := by
  ext g
  change Multiplicative.ofAdd ((fixedRadicalParameterHom q 0 g).toAdd 0) = 1 ↔
    fixedRadicalParameterHom q 0 g = 1
  constructor
  · intro h
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact congrArg Multiplicative.toAdd h
  · intro h
    rw [h]
    rfl

theorem rankTwoParameterHom_ker_eq_center (q : CFSG.PrimePower) :
    (rankTwoParameterHom q).ker = Subgroup.center (fixedRadical q 0) := by
  rw [rankTwoParameterHom_ker, fixedRadical_center_eq_kernel]

def rankTwoFirstLayerAutHom (q : CFSG.PrimePower) :
    MulAut (fixedRadical q 0) →* AddAut (q.Extension 2) :=
  CFSGCentralQuotientAutomorphism.quotientAddAutHom
    (rankTwoParameterHom q) (rankTwoParameterHom_surjective q) (rankTwoParameterHom_ker_eq_center q)

theorem rankTwoFirstLayerAutHom_first (q : CFSG.PrimePower)
    (f : MulAut (fixedRadical q 0)) (g : fixedRadical q 0) :
    rankTwoFirstLayerAutHom q f ((rankTwoParameterHom q g).toAdd) =
      (rankTwoParameterHom q (f g)).toAdd :=
  CFSGCentralQuotientAutomorphism.quotientAddAut_first
    (rankTwoParameterHom q) (rankTwoParameterHom_surjective q)
    (rankTwoParameterHom_ker_eq_center q) f g

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
