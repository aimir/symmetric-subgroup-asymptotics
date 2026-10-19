import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
import SymmetricSubgroupAsymptotics.NoTernaryQuotientFourthPowerWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
/-! Literal short identities selected in the original row202 alphabet.
The kernel, derived subgroup and normal denominators are not replaced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row202OriginalAbelianAxes
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
private def original : Fin 6 → row202Interface.top := closureGenerators row202Generators
private def normTwo (j : Fin 6) (w : DerivedGeneratorWord (Fin 6)) : DerivedGeneratorWord (Fin 6) :=
  .mul (.mul .one w) (.conj j w)
private def normThree (j : Fin 6) (w : DerivedGeneratorWord (Fin 6)) : DerivedGeneratorWord (Fin 6) :=
  .mul (normTwo j w) (.conj j (.conj j w))
private def normFour (j : Fin 6) (w : DerivedGeneratorWord (Fin 6)) : DerivedGeneratorWord (Fin 6) :=
  .mul (normThree j w) (.conj j (.conj j (.conj j w)))
def derived : Fin 6 → DerivedGeneratorWord (Fin 6) :=
  ![normThree 3 (.comm 0 2),normTwo 2 (.comm 0 2),.one,
    .inv (normFour 3 (.comm 2 5)),normThree 4 (.comm 2 5),.one]
private def correction (i : Fin 6) : row202Interface.top :=
  if i=2 then original 2 else if i=5 then original 5 else 1
private theorem identities (i : Fin 6) : original i=(derived i).eval original*correction i := by
  apply Subtype.ext
  revert i
  decide +kernel
private theorem killed (w : DerivedGeneratorWord (Fin 6)) :
    TwoAxisAbelianizationCover.q (w.eval original)=1 :=
  (QuotientGroup.eq_one_iff _).mpr (w.eval_mem_commutator original)

theorem generator_axes (i : Fin 6) : TwoAxisAbelianizationCover.q (original i)∈
    TwoAxisAbelianizationCover.Left (original 2) ⊔ TwoAxisAbelianizationCover.Right (original 5) := by
  let q : row202Interface.top →* row202Interface.top ⧸ commutator row202Interface.top :=
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
  · change q 1∈_
    rw [q.map_one]
    exact Subgroup.one_mem _
  · change q 1∈_
    rw [q.map_one]
    exact Subgroup.one_mem _
  · change q (original 5)∈_
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
def cover := TwoAxisAbelianizationCover.cover (original 2) (original 5)
theorem cover_surjective : Function.Surjective cover :=
  TwoAxisAbelianizationCover.cover_surjective (original 2) (original 5) original
    (closureGenerators_full _) generator_axes
private def fourthWords : Fin 6 → DerivedGeneratorWord (Fin 6) :=
  ![.one,.one,.inv (.mul .one (.comm 2 4)),derived 3,.one,.one]
theorem noTernary : NoTernaryQuotient row202Interface.top :=
  NoTernaryQuotientFourthPowerWords.of_generators original (closureGenerators_full _)
    fourthWords (by intro i; apply Subtype.ext; revert i; decide +kernel)
end SymmetricSubgroupAsymptotics.Row202OriginalAbelianAxes
