import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineProjectiveRepresentation
import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath

/-!
# The degree-nine six-point product action

This file realizes the actual projective image of a degree-nine affine
complement, times a binary scalar, as a faithful permutation group on six
points.  It is separated from the quotient-counting construction to keep
each Lean check within the workspace memory ceiling.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

private abbrev C2 := Multiplicative (ZMod 2)

variable {L : Type} [Group L] [MulAction L (Fin 9)] [Finite L]
  [FaithfulSMul L (Fin 9)]

/-- The direct-sum action of `S₄ × C₂` on four plus two points. -/
def degreeNineS4C2Action :
    Equiv.Perm (Fin 4) × C2 →* Equiv.Perm (Fin 6) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 4)) finSumFinEquiv).trans
      finSumFinEquiv).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin 4) (Fin 1 ⊕ Fin 1)).comp
      ((MonoidHom.id _).prodMap (C2Wreath.blockSwap (Fin 1))))

theorem degreeNineS4C2Action_injective :
    Function.Injective degreeNineS4C2Action := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hsum : (Equiv.Perm.sumCongrHom (Fin 4) (Fin 1 ⊕ Fin 1))
      (((MonoidHom.id _).prodMap (C2Wreath.blockSwap (Fin 1))) a) = 1 := by
    apply (((Equiv.sumCongr (Equiv.refl (Fin 4)) finSumFinEquiv).trans
      finSumFinEquiv).permCongrHom).injective
    rw [map_one]
    exact ha
  have hpair := Equiv.Perm.sumCongrHom_injective (hsum.trans (map_one _).symm)
  have hleft : a.1 = 1 := congrArg Prod.fst hpair
  have hright : C2Wreath.blockSwap (Fin 1) a.2 = 1 := congrArg Prod.snd hpair
  refine Prod.ext hleft ?_
  rcases C2Wreath.cases a.2 with h | h
  · exact h
  · exfalso
    rw [h, C2Wreath.blockSwap] at hright
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, C2Wreath.gen_ne_one,
      if_false] at hright
    have := congrArg (fun sigma : Equiv.Perm (Fin 1 ⊕ Fin 1) =>
      sigma (Sum.inl 0)) hright
    simp at this

/-- The actual projective image times `C₂`, acting on `4 + 2` points. -/
def degreeNineProductAction
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    P.DegreeNineProjectiveImage hprimitive x × C2 →*
      Equiv.Perm (Fin 6) :=
  degreeNineS4C2Action.comp
    ((P.DegreeNineProjectiveImage hprimitive x).subtype.prodMap (MonoidHom.id C2))

theorem degreeNineProductAction_injective
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    Function.Injective (P.degreeNineProductAction hprimitive x) := by
  intro a b hab
  have hab' := degreeNineS4C2Action_injective hab
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun y : Equiv.Perm (Fin 4) × C2 => y.1) hab'
  · exact congrArg (fun y : Equiv.Perm (Fin 4) × C2 => y.2) hab'

/-- The fixed faithful six-point comparator. -/
abbrev DegreeNineProductComparator
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :=
  (P.degreeNineProductAction hprimitive x).range

def degreeNineProductComparatorEquiv
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    P.DegreeNineProjectiveImage hprimitive x × C2 ≃*
      P.DegreeNineProductComparator hprimitive x :=
  MonoidHom.ofInjective (P.degreeNineProductAction_injective hprimitive x)

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
