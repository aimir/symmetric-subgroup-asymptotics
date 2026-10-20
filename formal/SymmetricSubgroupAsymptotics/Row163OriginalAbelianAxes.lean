import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
import SymmetricSubgroupAsymptotics.NoTernaryQuotientFourthPowerWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row163OriginalAbelianAxes
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
private def original := closureGenerators row163Generators
private def difference (w : DerivedGeneratorWord (Fin 5)) : DerivedGeneratorWord (Fin 5) :=
  .mul (.conj 2 w) w
private def active (i : Fin 5) : DerivedGeneratorWord (Fin 5) :=
  difference (difference (.comm 2 i))
def derived : Fin 5 → DerivedGeneratorWord (Fin 5) :=
  ![active 0,active 1,.mul (.comm 2 3) (.comm 2 3),.one,.one]
private theorem identities (i : Fin 3) : original (i.castLE (by decide : 3≤5))=(derived (i.castLE (by decide : 3≤5))).eval original := by
  apply Subtype.ext
  revert i
  decide +kernel
private theorem killed (w : DerivedGeneratorWord (Fin 5)) :
    TwoAxisAbelianizationCover.q (w.eval original)=1 :=
  (QuotientGroup.eq_one_iff _).mpr (w.eval_mem_commutator original)

theorem generator_axes (i : Fin 5) : TwoAxisAbelianizationCover.q (original i)∈
    TwoAxisAbelianizationCover.Left (original 3) ⊔ TwoAxisAbelianizationCover.Right (original 4) := by
  let q : row163Interface.top →* row163Interface.top ⧸ commutator row163Interface.top :=
    TwoAxisAbelianizationCover.q
  have h (j : Fin 3) : q (original (j.castLE (by decide : 3≤5)))=1 := (congrArg q (identities j)).trans (killed _)
  fin_cases i
  · change q (original 0)∈_
    have hi := h 0
    change q (original 0)=1 at hi
    rw [hi]
    exact Subgroup.one_mem _
  · change q (original 1)∈_
    have hi := h 1
    change q (original 1)=1 at hi
    rw [hi]
    exact Subgroup.one_mem _
  · change q (original 2)∈_
    have hi := h 2
    change q (original 2)=1 at hi
    rw [hi]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
def cover := TwoAxisAbelianizationCover.cover (original 3) (original 4)
theorem cover_surjective : Function.Surjective cover :=
  TwoAxisAbelianizationCover.cover_surjective (original 3) (original 4) original
    (closureGenerators_full _) generator_axes

private def fourthWords : Fin 5 → DerivedGeneratorWord (Fin 5) :=
  ![.one,.one,.mul (.comm 2 3) (.comm 2 3),.one,.one]
theorem noTernary : NoTernaryQuotient row163Interface.top :=
  NoTernaryQuotientFourthPowerWords.of_generators original (closureGenerators_full _)
    fourthWords (by intro i; apply Subtype.ext; revert i; decide +kernel)
end SymmetricSubgroupAsymptotics.Row163OriginalAbelianAxes
