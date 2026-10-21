import SymmetricSubgroupAsymptotics.S8Seed29LowModels

/-! Actual selected-normalizer invariance of the middle atom above8T29.
Both generator inclusions are checked by ordinary words. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed29LowNormalizer5
open S8Seed29LeftCosets

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed29NormalizerRoots.normalizer)
    (S8Seed29LowModels.generators 5) (S8Seed29LowModels.generators 5) where
  forward := {
    words := ![(.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 4) (.generator 4))), (.mul (.generator 4) (.mul (.generator 1) (.generator 4))), (.generator 2), (.mul (.generator 0) (.mul (.generator 5) (.generator 0))), (.generator 4), (.generator 5)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 4) (.generator 4))), (.mul (.generator 4) (.mul (.generator 1) (.generator 4))), (.generator 2), (.mul (.generator 0) (.mul (.generator 5) (.generator 0))), (.generator 4), (.generator 5)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : MulAut.conj S8Seed29NormalizerRoots.normalizer •
    S8Seed29LowModels.rows 5 = S8Seed29LowModels.rows 5 := by
  change (S8Seed29LowModels.rows 5).map
    (MulAut.conj S8Seed29NormalizerRoots.normalizer).toMonoidHom = _
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed29LowNormalizer5
end
