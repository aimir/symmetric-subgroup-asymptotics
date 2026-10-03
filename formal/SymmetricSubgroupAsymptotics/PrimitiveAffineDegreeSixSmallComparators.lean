import SymmetricSubgroupAsymptotics.Non2PreE7SelfComparatorSource
import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath

/-!
# Small faithful comparators for two degree-six affine cells

The regular `S₃` cell and the `S₃ × C₂` cell have faithful actions of
degrees three and five.  At retained physical width six those smaller
actions are admissible self-comparators.  This file packages the two model
constructions independently of the finite block-cell classifier.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev C2 := Multiplicative (ZMod 2)

/-- The disjoint natural actions of `S₃` and `C₂` on three plus two
points. -/
def s3c2Action :
    Equiv.Perm (Fin 3) × C2 →* Equiv.Perm (Fin 5) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 3)) finSumFinEquiv).trans
      finSumFinEquiv).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin 3) (Fin 1 ⊕ Fin 1)).comp
      ((MonoidHom.id _).prodMap (C2Wreath.blockSwap (Fin 1))))

theorem s3c2Action_injective : Function.Injective s3c2Action := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hsum : (Equiv.Perm.sumCongrHom (Fin 3) (Fin 1 ⊕ Fin 1))
      (((MonoidHom.id _).prodMap (C2Wreath.blockSwap (Fin 1))) x) = 1 := by
    apply (((Equiv.sumCongr (Equiv.refl (Fin 3)) finSumFinEquiv).trans
      finSumFinEquiv).permCongrHom).injective
    rw [map_one]
    exact hx
  have hpair := Equiv.Perm.sumCongrHom_injective
    (hsum.trans (map_one _).symm)
  have hleft : x.1 = 1 := congrArg Prod.fst hpair
  have hright : C2Wreath.blockSwap (Fin 1) x.2 = 1 :=
    congrArg Prod.snd hpair
  refine Prod.ext hleft ?_
  rcases C2Wreath.cases x.2 with h | h
  · exact h
  · exfalso
    rw [h, C2Wreath.blockSwap] at hright
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, C2Wreath.gen_ne_one,
      if_false] at hright
    have := congrArg (fun sigma : Equiv.Perm (Fin 1 ⊕ Fin 1) =>
      sigma (Sum.inl 0)) hright
    simp at this

/-- An abstract `S₃` model for the retained six-point action. -/
structure PreE7DegreeSixS3Source (U : PreE7NonPairActionClass 6) : Type where
  equiv : preE7NonPairAction 6 U ≃* Equiv.Perm (Fin 3)

namespace PreE7DegreeSixS3Source

variable {U : PreE7NonPairActionClass 6} (S : PreE7DegreeSixS3Source U)

/-- The natural three-point action gives the completed ambient source. -/
noncomputable def source : PreE7RankTailSourceOrYonedaTopData 6 U :=
  DegreeSixSelfComparatorSource.source U 3 (by norm_num) (by norm_num)
    S.equiv.toMonoidHom S.equiv.injective

end PreE7DegreeSixS3Source

/-- An abstract `S₃ × C₂` model for the retained six-point action. -/
structure PreE7DegreeSixS3C2Source (U : PreE7NonPairActionClass 6) : Type where
  equiv : preE7NonPairAction 6 U ≃* Equiv.Perm (Fin 3) × C2

namespace PreE7DegreeSixS3C2Source

variable {U : PreE7NonPairActionClass 6} (S : PreE7DegreeSixS3C2Source U)

/-- The disjoint five-point action gives the completed ambient source. -/
noncomputable def source : PreE7RankTailSourceOrYonedaTopData 6 U :=
  DegreeSixSelfComparatorSource.source U 5 (by norm_num) (by norm_num)
    (s3c2Action.comp S.equiv.toMonoidHom)
    (s3c2Action_injective.comp S.equiv.injective)

end PreE7DegreeSixS3C2Source

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
