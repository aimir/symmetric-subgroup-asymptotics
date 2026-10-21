import SymmetricSubgroupAsymptotics.S8Seed4LowModels

/-! One actual low-row equality certified by ordinary words in both
directions. No cardinality or catalogue correspondence is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer8
open S8Seed4LeftCosets S8Seed4LowModels

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed4NormalizerRoots.normalizer)
    (generators 8) (generators 4) where
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

theorem normalizer_image : MulAut.conj S8Seed4NormalizerRoots.normalizer • rows 8 = rows 4 := by
  change (rows 8).map (MulAut.conj S8Seed4NormalizerRoots.normalizer).toMonoidHom = rows 4
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer8
end
