import SymmetricSubgroupAsymptotics.S8Seed6LowModels

/-! Actual low-root equality and the selected normalizer's swap of the
 two literal low rows. Bidirectional ordinary words prove each equality. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed6LowRelations
open S8Seed6LeftCosets S8Seed6LowModels

def root89Certificate : FiniteGeneratorEquivWordCertificate (MulEquiv.refl Ambient)
    (rootGenerators 89) (S8Seed6LowModels.generators 1) where
  forward := {
    words := ![(.mul (.mul (.generator 2) (.mul (.generator 0) (.generator 1))) (.mul (.mul (.generator 1) (.generator 1)) (.mul (.generator 0) (.generator 1)))), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.inv (.generator 1)) (.mul (.generator 0) (.inv (.generator 1)))) (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 0) (.generator 1)))), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
def normalizerOneCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed6NormalizerRoots.normalizer)
    (S8Seed6LowModels.generators 1) (S8Seed6LowModels.generators 2) where
  forward := {
    words := ![(.mul (.mul (.inv (.generator 0)) (.generator 1)) (.mul (.inv (.generator 0)) (.generator 1))), (.mul (.generator 1) (.mul (.generator 1) (.generator 1))), (.mul (.mul (.generator 0) (.generator 0)) (.mul (.generator 0) (.generator 0)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 0) (.mul (.inv (.generator 1)) (.inv (.generator 1)))) (.mul (.mul (.generator 0) (.inv (.generator 1))) (.mul (.inv (.generator 1)) (.inv (.generator 1))))), (.mul (.generator 1) (.mul (.generator 1) (.generator 1))), (.mul (.mul (.generator 1) (.generator 1)) (.mul (.generator 1) (.mul (.generator 1) (.generator 2))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
def normalizerTwoCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed6NormalizerRoots.normalizer)
    (S8Seed6LowModels.generators 2) (S8Seed6LowModels.generators 1) where
  forward := {
    words := ![(.mul (.mul (.generator 1) (.mul (.generator 1) (.generator 1))) (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 1) (.generator 0)))), (.mul (.generator 1) (.mul (.generator 1) (.generator 1))), (.mul (.mul (.generator 1) (.generator 1)) (.mul (.generator 1) (.mul (.generator 1) (.generator 2))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 0) (.generator 1))), (.mul (.generator 1) (.mul (.generator 1) (.generator 1))), (.mul (.mul (.generator 0) (.generator 0)) (.mul (.generator 0) (.generator 0)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem root89_eq : Subgroup.closure (Set.range (rootGenerators 89)) = rows 1 := by
  have h := root89Certificate.map_closure_eq
  change (Subgroup.closure (Set.range (rootGenerators 89))).map
    (MonoidHom.id Ambient) = rows 1 at h
  rw [Subgroup.map_id] at h
  exact h

theorem normalizer_one : MulAut.conj S8Seed6NormalizerRoots.normalizer • rows 1 = rows 2 := by
  change (rows 1).map (MulAut.conj S8Seed6NormalizerRoots.normalizer).toMonoidHom = rows 2
  exact normalizerOneCertificate.map_closure_eq

theorem normalizer_two : MulAut.conj S8Seed6NormalizerRoots.normalizer • rows 2 = rows 1 := by
  change (rows 2).map (MulAut.conj S8Seed6NormalizerRoots.normalizer).toMonoidHom = rows 1
  exact normalizerTwoCertificate.map_closure_eq

theorem inverse_normalizer_two :
    MulAut.conj (S8Seed6NormalizerRoots.normalizer⁻¹) • rows 2 = rows 1 := by
  have h := congrArg (fun W : Subgroup Ambient =>
    MulAut.conj (S8Seed6NormalizerRoots.normalizer⁻¹) • W) normalizer_one
  simpa only [map_inv, inv_smul_smul] using h.symm

end SymmetricSubgroupAsymptotics.S8Seed6LowRelations
end
