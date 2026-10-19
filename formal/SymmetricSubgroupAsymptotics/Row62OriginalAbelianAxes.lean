import SymmetricSubgroupAsymptotics.Row62OriginalQuartetFrame
import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row62OriginalAbelianAxes
open Row62OriginalQuartetFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
private def d : DerivedGeneratorWord (Fin 3) := .comm 0 1
private def cd : DerivedGeneratorWord (Fin 3) := .conj 1 d
private def derived : Fin 2 → DerivedGeneratorWord (Fin 3) :=
  ![.mul (.mul d d) (.mul cd (.mul cd cd)),.comm 2 1]
private theorem identities (i : Fin 2) :
    original (i.castLE (by decide : 2≤3))=(derived i).eval original := by
  apply Subtype.ext
  revert i
  decide +kernel
private theorem killed (w : DerivedGeneratorWord (Fin 3)) :
    TwoAxisAbelianizationCover.q (w.eval original)=1 :=
  (QuotientGroup.eq_one_iff _).mpr (w.eval_mem_commutator original)
theorem generator_axes (i : Fin 3) : TwoAxisAbelianizationCover.q (original i)∈
    TwoAxisAbelianizationCover.Left (original 2) ⊔ TwoAxisAbelianizationCover.Right (original 2) := by
  let q : Row62Top →* Row62Top ⧸ commutator Row62Top := TwoAxisAbelianizationCover.q
  have h (j : Fin 2) : q (original (j.castLE (by decide : 2≤3)))=1 :=
    (congrArg q (identities j)).trans (killed _)
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
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
def cover := TwoAxisAbelianizationCover.cover (original 2) (original 2)
theorem cover_surjective : Function.Surjective cover :=
  TwoAxisAbelianizationCover.cover_surjective (original 2) (original 2) original
    (closureGenerators_full _) generator_axes
end SymmetricSubgroupAsymptotics.Row62OriginalAbelianAxes
