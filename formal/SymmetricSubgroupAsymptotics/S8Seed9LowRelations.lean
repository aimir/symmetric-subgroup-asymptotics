import SymmetricSubgroupAsymptotics.S8Seed9LowModels

/-! Actual ordinary words prove both selected-normalizer interchanges. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed9LowRelations
open S8Seed9LeftCosets S8Seed9LowModels

def normalizerOneCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed9NormalizerRoots.normalizer)
    (S8Seed9LowModels.generators 1) (S8Seed9LowModels.generators 3) where
  forward := {
    words := ![(.generator 0), (.generator 1), (.generator 2), (.generator 3), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 0), (.generator 1), (.generator 2), (.generator 3), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizer_one : MulAut.conj S8Seed9NormalizerRoots.normalizer • rows 1 = rows 3 := by
  change (rows 1).map (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom = rows 3
  exact normalizerOneCertificate.map_closure_eq
def normalizerTwoCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed9NormalizerRoots.normalizer)
    (S8Seed9LowModels.generators 2) (S8Seed9LowModels.generators 4) where
  forward := {
    words := ![(.generator 0), (.generator 1), (.generator 2), (.generator 3), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 0), (.generator 1), (.generator 2), (.generator 3), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizer_two : MulAut.conj S8Seed9NormalizerRoots.normalizer • rows 2 = rows 4 := by
  change (rows 2).map (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom = rows 4
  exact normalizerTwoCertificate.map_closure_eq
def normalizerThreeCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed9NormalizerRoots.normalizer)
    (S8Seed9LowModels.generators 3) (S8Seed9LowModels.generators 1) where
  forward := {
    words := ![(.mul (.generator 0) (.mul (.generator 2) (.generator 3))), (.generator 1), (.generator 2), (.generator 3), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 0) (.mul (.generator 2) (.generator 3))), (.generator 1), (.generator 2), (.generator 3), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizer_three : MulAut.conj S8Seed9NormalizerRoots.normalizer • rows 3 = rows 1 := by
  change (rows 3).map (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom = rows 1
  exact normalizerThreeCertificate.map_closure_eq
def normalizerFourCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed9NormalizerRoots.normalizer)
    (S8Seed9LowModels.generators 4) (S8Seed9LowModels.generators 2) where
  forward := {
    words := ![(.mul (.generator 0) (.generator 3)), (.generator 1), (.generator 2), (.generator 3), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 0) (.generator 3)), (.generator 1), (.generator 2), (.generator 3), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizer_four : MulAut.conj S8Seed9NormalizerRoots.normalizer • rows 4 = rows 2 := by
  change (rows 4).map (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom = rows 2
  exact normalizerFourCertificate.map_closure_eq

theorem inverse_normalizer_three : MulAut.conj (S8Seed9NormalizerRoots.normalizer⁻¹) • rows 3 = rows 1 := by
  have h:=congrArg (fun W : Subgroup Ambient => MulAut.conj (S8Seed9NormalizerRoots.normalizer⁻¹) • W) normalizer_one
  simpa only [map_inv,inv_smul_smul] using h.symm

theorem inverse_normalizer_four : MulAut.conj (S8Seed9NormalizerRoots.normalizer⁻¹) • rows 4 = rows 2 := by
  have h:=congrArg (fun W : Subgroup Ambient => MulAut.conj (S8Seed9NormalizerRoots.normalizer⁻¹) • W) normalizer_two
  simpa only [map_inv,inv_smul_smul] using h.symm

end SymmetricSubgroupAsymptotics.S8Seed9LowRelations
end
