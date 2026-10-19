import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
import SymmetricSubgroupAsymptotics.NoTernaryQuotientFourthPowerWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
/-! Literal short identities verified in the original row160 alphabet.
The kernel, derived subgroup and normal denominators are not replaced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row160OriginalAbelianAxes
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
private def original : Fin 4 → row160Interface.top := closureGenerators row160Generators
private def difference (w : DerivedGeneratorWord (Fin 4)) : DerivedGeneratorWord (Fin 4) :=
  .mul (.conj 1 w) w
def derived : Fin 4 → DerivedGeneratorWord (Fin 4) :=
  ![difference (difference (.comm 0 1)),
    .mul (.conj 1 (difference (difference (.comm 0 1)))) (.mul (.comm 1 2) (.comm 1 2)),
    .one,.one]
private def correction (i : Fin 4) : row160Interface.top :=
  if i=2 then original 2 else if i=3 then original 3 else 1
private theorem identities (i : Fin 4) : original i=(derived i).eval original*correction i := by
  apply Subtype.ext
  revert i
  decide +kernel
private theorem killed (w : DerivedGeneratorWord (Fin 4)) :
    TwoAxisAbelianizationCover.q (w.eval original)=1 :=
  (QuotientGroup.eq_one_iff _).mpr (w.eval_mem_commutator original)

theorem generator_axes (i : Fin 4) : TwoAxisAbelianizationCover.q (original i)∈
    TwoAxisAbelianizationCover.Left (original 2) ⊔ TwoAxisAbelianizationCover.Right (original 3) := by
  let q : row160Interface.top →* row160Interface.top ⧸ commutator row160Interface.top :=
    TwoAxisAbelianizationCover.q
  have h : q (original i)=q (correction i) := by
    calc
      q (original i)=q ((derived i).eval original*correction i) := congrArg q (identities i)
      _=q (correction i) := by rw [q.map_mul,killed,one_mul]
  change q (original i)∈_
  rw [h]
  fin_cases i
  · change q 1∈_
    rw [q.map_one]
    exact Subgroup.one_mem _
  · change q 1∈_
    rw [q.map_one]
    exact Subgroup.one_mem _
  · change q (original 2)∈_
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · change q (original 3)∈_
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
def cover := TwoAxisAbelianizationCover.cover (original 2) (original 3)
theorem cover_surjective : Function.Surjective cover :=
  TwoAxisAbelianizationCover.cover_surjective (original 2) (original 3) original
    (closureGenerators_full _) generator_axes
private def fourthWords : Fin 4 → DerivedGeneratorWord (Fin 4) :=
  ![.one,derived 1,.one,.one]
theorem noTernary : NoTernaryQuotient row160Interface.top :=
  NoTernaryQuotientFourthPowerWords.of_generators original (closureGenerators_full _)
    fourthWords (by intro i; apply Subtype.ext; revert i; decide +kernel)
end SymmetricSubgroupAsymptotics.Row160OriginalAbelianAxes
