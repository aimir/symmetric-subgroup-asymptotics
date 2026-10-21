import SymmetricSubgroupAsymptotics.S8Seed8LowModels

/-! Actual ordinary words prove the normalizer interchange of the two
literal48-element low rows. No fixation or order recognition is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed8LowRelations
open S8Seed8LeftCosets S8Seed8LowModels

def normalizerOneCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed8NormalizerRoots.normalizer)
    (S8Seed8LowModels.generators 1) (S8Seed8LowModels.generators 2) where
  forward := {
    words := ![(.generator 0), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 0), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
def normalizerTwoCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed8NormalizerRoots.normalizer)
    (S8Seed8LowModels.generators 2) (S8Seed8LowModels.generators 1) where
  forward := {
    words := ![(.mul (.generator 0) (.mul (.generator 0) (.generator 0))), (.generator 1), (.mul (.generator 0) (.mul (.generator 0) (.inv (.generator 1))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 0) (.mul (.generator 0) (.generator 0))), (.generator 1), (.mul (.generator 0) (.mul (.generator 0) (.inv (.generator 1))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizer_one : MulAut.conj S8Seed8NormalizerRoots.normalizer • rows 1 = rows 2 := by
  change (rows 1).map (MulAut.conj S8Seed8NormalizerRoots.normalizer).toMonoidHom = rows 2
  exact normalizerOneCertificate.map_closure_eq

theorem normalizer_two : MulAut.conj S8Seed8NormalizerRoots.normalizer • rows 2 = rows 1 := by
  change (rows 2).map (MulAut.conj S8Seed8NormalizerRoots.normalizer).toMonoidHom = rows 1
  exact normalizerTwoCertificate.map_closure_eq

theorem inverse_normalizer_two : MulAut.conj (S8Seed8NormalizerRoots.normalizer⁻¹) • rows 2 = rows 1 := by
  have h:=congrArg (fun W : Subgroup Ambient => MulAut.conj (S8Seed8NormalizerRoots.normalizer⁻¹) • W) normalizer_one
  simpa only [map_inv,inv_smul_smul] using h.symm

end SymmetricSubgroupAsymptotics.S8Seed8LowRelations
end
