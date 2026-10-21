import SymmetricSubgroupAsymptotics.S8Seed5LowModels

/-! One actual low-row equality certified by ordinary words in both
directions. No cardinality or catalogue correspondence is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed5LowNormalizer3
open S8Seed5LeftCosets S8Seed5LowModels

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed5NormalizerRoots.normalizer)
    (generators 3) (generators 4) where
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

theorem normalizer_image : MulAut.conj S8Seed5NormalizerRoots.normalizer • rows 3 = rows 4 := by
  change (rows 3).map (MulAut.conj S8Seed5NormalizerRoots.normalizer).toMonoidHom = rows 4
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed5LowNormalizer3
end
