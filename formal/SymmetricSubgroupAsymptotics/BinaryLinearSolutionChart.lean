import SymmetricSubgroupAsymptotics.BinaryLinearConstraintCertificate
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces

/-! A sparse row certificate places every actual solution of linear carry
constraints inside a reversible coordinate chart. Checked basis identities
then factor the solution through literal gauge vectors. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

variable {w d a g : ℕ}

/-- Each row is the actual coordinate defect of the reversible chart. -/
def binaryCoordinateDefectRows (C : BinaryCoordinateSpace w d) :
    Fin w → Fin w → ZMod 2 :=
  fun j i => ((Pi.single i 1 : Fin w → ZMod 2) - C.inclusion (C.coordinates (Pi.single i 1))) j

theorem binaryCoordinateDefect_dotProduct
    (C : BinaryCoordinateSpace w d) (j : Fin w) (x : Fin w → ZMod 2) :
    dotProduct (binaryCoordinateDefectRows C j) x =
      (x - C.inclusion (C.coordinates x)) j := by
  let f : (Fin w → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj j).comp
      (LinearMap.id - C.inclusion.comp C.coordinates)
  have he : binaryRowFunctional (binaryCoordinateDefectRows C j) = f :=
    binaryLinearFunctional_ext_basis (fun i => by
      change dotProduct (binaryCoordinateDefectRows C j) (Pi.single i 1) =
        ((Pi.single i 1 : Fin w → ZMod 2) - C.inclusion (C.coordinates (Pi.single i 1))) j
      rw [dotProduct_single_one]
      rfl)
  exact congrArg (fun z : ((Fin w → ZMod 2) →ₗ[ZMod 2] ZMod 2) => z x) he

/-- No enumeration of assignments is needed: every literal carry solution
lies in the checked chart by sparse row identities. -/
theorem binaryCoordinate_mem_of_constraints
    (C : BinaryCoordinateSpace w d) (input : Fin a → Fin w → ZMod 2)
    (cert : BinaryLinearConstraintCertificate input (binaryCoordinateDefectRows C))
    (x : Fin w → ZMod 2) (hx : ∀ i, dotProduct (input i) x = 0) :
    x ∈ C.space := by
  apply (C.mem_iff x).mpr
  funext j
  have hz := cert.target_dotProduct_eq_zero x hx j
  rw [binaryCoordinateDefect_dotProduct] at hz
  exact (sub_eq_zero.mp hz).symm

/-- A retained linear factorization gives actual gauge coordinates for
every solution in C, rather than merely reporting a matrix rank. -/
structure BinaryCoordinateFactorCertificate
    (C : BinaryCoordinateSpace w d)
    (gauge : (Fin g → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)) where
  lift : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin g → ZMod 2)
  basis_eq : ∀ i, gauge (lift (Pi.single i 1)) = C.inclusion (Pi.single i 1)

namespace BinaryCoordinateFactorCertificate

variable {C : BinaryCoordinateSpace w d}
  {gauge : (Fin g → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)}
  (cert : BinaryCoordinateFactorCertificate C gauge)

include cert

theorem inclusion_eq_factor : gauge.comp cert.lift = C.inclusion := by
  apply LinearMap.pi_ext
  intro i c
  have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  simp only [LinearMap.comp_apply, hs, map_smul, cert.basis_eq]

theorem exists_actual_gauge_coordinates (x : Fin w → ZMod 2) (hx : x ∈ C.space) :
    ∃ y : Fin g → ZMod 2, gauge y = x := by
  obtain ⟨v, rfl⟩ := hx
  refine ⟨cert.lift v, ?_⟩
  exact congrArg (fun f : ((Fin d → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)) => f v)
    cert.inclusion_eq_factor

end BinaryCoordinateFactorCertificate
end SymmetricSubgroupAsymptotics
