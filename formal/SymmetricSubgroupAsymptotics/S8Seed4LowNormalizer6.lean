import SymmetricSubgroupAsymptotics.S8Seed4LowModels

/-! One actual low-row equality certified by ordinary words in both
directions. No cardinality or catalogue correspondence is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer6
open S8Seed4LeftCosets S8Seed4LowModels

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed4NormalizerRoots.normalizer)
    (generators 6) (generators 6) where
  forward := {
    words := ![(.mul (.generator 2) (.mul (.generator 0) (.generator 2))), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 2) (.mul (.generator 0) (.generator 2))), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizer_image : MulAut.conj S8Seed4NormalizerRoots.normalizer • rows 6 = rows 6 := by
  change (rows 6).map (MulAut.conj S8Seed4NormalizerRoots.normalizer).toMonoidHom = rows 6
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer6
end
