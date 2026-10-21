import SymmetricSubgroupAsymptotics.CFSGSerreDiagramQuotient

/-! The existing integral Serre lattice is preserved by an actual diagram
permutation. The proof uses its original least-stable-submodule definition,
so no second lattice or finite-type basis is substituted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreDiagram
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

theorem generator_mem_integralLattice (g : CartanMatrix.Generators (Fin n)) :
    generator A g ∈ integralLattice A := by
  rw [integralLattice, Submodule.mem_sInf]
  intro L hL
  exact hL.1 g

/-- Induction/minimality for the same divided-power-stable lattice. -/
theorem integralLattice_le_of_stable (L : Submodule ℤ (RationalLie A))
    (hgen : ∀ g, generator A g ∈ L)
    (hstable : ∀ negative i k x, x ∈ L → dividedPower A negative i k x ∈ L) :
    integralLattice A ≤ L := by
  exact sInf_le ⟨hgen, hstable⟩

def latticeGenerator (g : CartanMatrix.Generators (Fin n)) : integralLattice A :=
  ⟨generator A g, generator_mem_integralLattice A g⟩

variable (p : Equiv.Perm (Fin n)) (hA : ∀ i j, A (p i) (p j) = A i j)
include hA

theorem rationalEquiv_preserves_lattice (x : RationalLie A) (hx : x ∈ integralLattice A) :
    rationalEquiv A p hA x ∈ integralLattice A := by
  let S := (integralLattice A).comap
    ((rationalEquiv A p hA).toLinearEquiv.toLinearMap.restrictScalars ℤ)
  have hle : integralLattice A ≤ S := by
    apply integralLattice_le_of_stable A S
    · intro g
      change rationalEquiv A p hA (generator A g) ∈ integralLattice A
      rw [rationalEquiv_generator]
      exact generator_mem_integralLattice A _
    · intro negative i k y hy
      change rationalEquiv A p hA y ∈ integralLattice A at hy
      change rationalEquiv A p hA (dividedPower A negative i k y) ∈ integralLattice A
      rw [rationalEquiv_dividedPower]
      exact dividedPower_mem A negative (p i) k _ hy
  exact hle hx

def integralMap : integralLattice A →ₗ[ℤ] integralLattice A :=
  ((rationalEquiv A p hA).toLinearEquiv.toLinearMap.restrictScalars ℤ).restrict
    (rationalEquiv_preserves_lattice A p hA)

def integralEquiv : integralLattice A ≃ₗ[ℤ] integralLattice A where
  __ := integralMap A p hA
  invFun := integralMap A p.symm (preserves_symm A p hA)
  left_inv := by
    intro x
    apply Subtype.ext
    exact rationalMap_inverse_apply A p hA x.val
  right_inv := by
    intro x
    apply Subtype.ext
    simpa only [Equiv.symm_symm] using
      rationalMap_inverse_apply A p.symm (preserves_symm A p hA) x.val

@[simp] theorem integralEquiv_coe_apply (x : integralLattice A) :
    (integralEquiv A p hA x).val = rationalEquiv A p hA x.val := rfl

@[simp] theorem integralEquiv_generator (g : CartanMatrix.Generators (Fin n)) :
    integralEquiv A p hA (latticeGenerator A g) = latticeGenerator A (nodeRename p g) := by
  apply Subtype.ext
  exact rationalEquiv_generator A p hA g

theorem integralEquiv_integralOperator (negative : Bool) (i : Fin n) (k : ℕ)
    (x : integralLattice A) :
    integralEquiv A p hA (integralOperator A negative i k x) =
      integralOperator A negative (p i) k (integralEquiv A p hA x) := by
  apply Subtype.ext
  exact rationalEquiv_dividedPower A p hA negative i k x.val

end SymmetricSubgroupAsymptotics.CFSGSerreDiagram
