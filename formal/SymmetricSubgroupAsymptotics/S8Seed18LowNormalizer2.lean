import SymmetricSubgroupAsymptotics.S8Seed18LowModels

/-! Actual selected-normalizer invariance of the selected atom above8T18.
Both generator inclusions are checked by ordinary words. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed18LowNormalizer2
open S8Seed18LeftCosets

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed18NormalizerRoots.normalizer)
    (S8Seed18LowModels.generators 2) (S8Seed18LowModels.generators 2) where
  forward := {
    words := ![(.inv (.generator 0)), (.generator 2), (.generator 1), (.generator 3), (.mul (.generator 2) (.generator 5)), (.mul (.generator 1) (.generator 4))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.inv (.generator 0)), (.generator 2), (.generator 1), (.generator 3), (.mul (.generator 2) (.generator 5)), (.mul (.generator 1) (.generator 4))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : MulAut.conj S8Seed18NormalizerRoots.normalizer •
    S8Seed18LowModels.rows 2 = S8Seed18LowModels.rows 2 := by
  change (S8Seed18LowModels.rows 2).map
    (MulAut.conj S8Seed18NormalizerRoots.normalizer).toMonoidHom = _
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed18LowNormalizer2
end
