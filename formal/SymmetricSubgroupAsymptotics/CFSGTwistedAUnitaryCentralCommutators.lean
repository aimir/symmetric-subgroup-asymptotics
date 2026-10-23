import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergCommutator
import SymmetricSubgroupAsymptotics.CFSGTwistedA2RadicalFirstLayer

/-! Every element of the ACTUAL radical centre is one commutator.
Consequently a first-layer-trivial endomorphism fixes the whole centre.
This works in every characteristic, including the small field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

theorem centralRadical_eq_commutator (q : CFSG.PrimePower) (s : ℕ)
    (c : Multiplicative (centralParameters q s)) :
    ∃ x y : fixedRadical q s, ⁅x, y⁆ = centralRadicalHom q s c := by
  let v : Fin (s + 1) → q.Extension 2 := fun _ => 1
  have hv : v ≠ 0 := by
    intro he
    exact one_ne_zero (congrFun he 0)
  obtain ⟨w, hw⟩ := centralPair_surjective q s v hv c.toAdd
  obtain ⟨x, hx⟩ := fixedRadicalParameterHom_surjective q s (Multiplicative.ofAdd v)
  obtain ⟨y, hy⟩ := fixedRadicalParameterHom_surjective q s (Multiplicative.ofAdd w)
  refine ⟨x, y, ?_⟩
  rw [fixedRadical_commutator, hx, hy]
  change centralRadicalHom q s (Multiplicative.ofAdd (centralPair q s v w)) = centralRadicalHom q s c
  rw [hw, ofAdd_toAdd]

theorem endomorphism_fixes_centre_of_vector (q : CFSG.PrimePower) (s : ℕ)
    (f : fixedRadical q s →* fixedRadical q s)
    (hf : ∀ g, fixedRadicalParameterHom q s (f g) = fixedRadicalParameterHom q s g)
    (c : Multiplicative (centralParameters q s)) :
    f (centralRadicalHom q s c) = centralRadicalHom q s c := by
  obtain ⟨x, y, he⟩ := centralRadical_eq_commutator q s c
  calc
    f (centralRadicalHom q s c) = f ⁅x, y⁆ := congrArg f he.symm
    _ = ⁅f x, f y⁆ := map_commutatorElement f x y
    _ = ⁅x, y⁆ := by rw [fixedRadical_commutator, fixedRadical_commutator, hf x, hf y]
    _ = centralRadicalHom q s c := he

theorem rankTwo_vector_fixed_of_firstLayer_eq_one (q : CFSG.PrimePower)
    (f : MulAut (fixedRadical q 0)) (hf : rankTwoFirstLayerAutHom q f = 1)
    (g : fixedRadical q 0) : fixedRadicalParameterHom q 0 (f g) = fixedRadicalParameterHom q 0 g := by
  have he := rankTwoFirstLayerAutHom_first q f g
  rw [hf] at he
  change (rankTwoParameterHom q g).toAdd = (rankTwoParameterHom q (f g)).toAdd at he
  apply Multiplicative.toAdd.injective
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact he.symm

theorem rankTwo_firstLayer_kernel_fixes_centre (q : CFSG.PrimePower)
    (f : MulAut (fixedRadical q 0)) (hf : rankTwoFirstLayerAutHom q f = 1)
    (c : Multiplicative (centralParameters q 0)) :
    f (centralRadicalHom q 0 c) = centralRadicalHom q 0 c :=
  endomorphism_fixes_centre_of_vector q 0 f.toMonoidHom
    (rankTwo_vector_fixed_of_firstLayer_eq_one q f hf) c

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
