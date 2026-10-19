import SymmetricSubgroupAsymptotics.Row27OriginalQuartetFrame
import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row27OriginalAbelianAxes
open Row27OriginalQuartetFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
private theorem square_identity : original 0=(original 3)^2 := by
  apply Subtype.ext
  decide +kernel
private theorem commutator_identity : original 2=(DerivedGeneratorWord.comm 1 3).eval original := by
  apply Subtype.ext
  decide +kernel
 theorem generator_axes (i : Fin 4) : TwoAxisAbelianizationCover.q (original i)∈
    TwoAxisAbelianizationCover.Left (original 1) ⊔ TwoAxisAbelianizationCover.Right (original 3) := by
  fin_cases i
  · change TwoAxisAbelianizationCover.q (original 0)∈_
    rw [square_identity,map_pow]
    exact Subgroup.mem_sup_right ((TwoAxisAbelianizationCover.Right (original 3)).pow_mem
      (Subgroup.mem_zpowers _) 2)
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · change TwoAxisAbelianizationCover.q (original 2)∈_
    have hk : TwoAxisAbelianizationCover.q (original 2)=1 := by
      rw [commutator_identity]
      exact (QuotientGroup.eq_one_iff _).mpr
        ((DerivedGeneratorWord.comm (1 : Fin 4) 3).eval_mem_commutator original)
    rw [hk]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
 def cover := TwoAxisAbelianizationCover.cover (original 1) (original 3)
 theorem cover_surjective : Function.Surjective cover :=
  TwoAxisAbelianizationCover.cover_surjective (original 1) (original 3) original
    (closureGenerators_full _) generator_axes
end SymmetricSubgroupAsymptotics.Row27OriginalAbelianAxes
