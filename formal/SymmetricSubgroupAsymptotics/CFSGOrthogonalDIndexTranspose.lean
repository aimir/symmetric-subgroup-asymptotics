import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup

/-! Actual transpose stability of the original D elementary subgroup.
Transpose reverses products, so stability is proved as a subgroup
preimage with reversed multiplication, rather than asserted from a
classical-group name. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTranspose
open CFSGOrthogonalDSerreMatrices
variable (K : Type*) [CommRing K] (r : ℕ)

def transposeUnit (u : (Mat K r)ˣ) : (Mat K r)ˣ where
  val := (u : Mat K r).transpose
  inv := (↑(u⁻¹) : Mat K r).transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

@[simp] theorem transposeUnit_one : transposeUnit K r 1 = 1 := by
  apply Units.ext
  exact Matrix.transpose_one

theorem transposeUnit_mul (u v : (Mat K r)ˣ) :
    transposeUnit K r (u * v) = transposeUnit K r v * transposeUnit K r u := by
  apply Units.ext
  exact Matrix.transpose_mul _ _

theorem transposeUnit_inv (u : (Mat K r)ˣ) :
    transposeUnit K r u⁻¹ = (transposeUnit K r u)⁻¹ := by
  apply Units.ext
  rfl

theorem transposeUnit_root (neg : Bool) (i : Fin r) (a : K) :
    transposeUnit K r (rootTransvection K r neg i a) =
      rootTransvection K r (!neg) i a := by
  apply Units.ext
  cases neg <;>
    simp [transposeUnit, rootTransvection_val, rootMatrix, negative,
      Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
      Matrix.transpose_transpose]

def transposePreimage (H : Subgroup (Mat K r)ˣ) : Subgroup (Mat K r)ˣ where
  carrier := {u | transposeUnit K r u ∈ H}
  one_mem' := by
    change transposeUnit K r 1 ∈ H
    rw [transposeUnit_one]
    exact H.one_mem
  mul_mem' := by
    intro u v hu hv
    change transposeUnit K r (u * v) ∈ H
    rw [transposeUnit_mul]
    exact H.mul_mem hv hu
  inv_mem' := by
    intro u hu
    change transposeUnit K r u⁻¹ ∈ H
    rw [transposeUnit_inv]
    exact H.inv_mem hu

theorem transposeUnit_mem (u : (Mat K r)ˣ) (hu : u ∈ elementaryRootGroup K r) :
    transposeUnit K r u ∈ elementaryRootGroup K r := by
  have hle : elementaryRootGroup K r ≤ transposePreimage K r (elementaryRootGroup K r) := by
    apply (Subgroup.closure_le _).mpr
    rintro v ⟨neg, i, a, rfl⟩
    change transposeUnit K r (rootTransvection K r neg i a) ∈ elementaryRootGroup K r
    rw [transposeUnit_root]
    exact rootTransvection_mem K r (!neg) i a
  exact hle hu

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTranspose
