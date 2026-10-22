import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations

/-! Lie maps out of the literal rational Serre quotient are determined
by the actual H/E/F generators. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreGeneratorExt
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem hom_ext (f g : RationalLie A →ₗ⁅ℚ⁆ L)
    (h : ∀ i : CartanMatrix.Generators (Fin n), f (generator A i) = g (generator A i)) :
    f = g := by
  have he : f.comp (quotientMap A) = g.comp (quotientMap A) :=
    FreeLieAlgebra.hom_ext h
  apply LieHom.ext
  intro x
  obtain ⟨y, rfl⟩ := quotientMap_surjective A x
  exact congrArg (fun F : Free (n := n) →ₗ⁅ℚ⁆ L => F y) he

end SymmetricSubgroupAsymptotics.CFSGSerreGeneratorExt
