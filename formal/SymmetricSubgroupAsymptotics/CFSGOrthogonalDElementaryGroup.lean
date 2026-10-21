import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import SymmetricSubgroupAsymptotics.CFSGSquareZeroConjugation
import SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The independently defined natural D root-matrix group. It is not
identified by name with any full classical matrix group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices

def rootMatrix (R : Type*) [CommRing R] (r : ℕ) (neg : Bool) (i : Fin r) : Mat R r :=
  if neg then negative R r i else positive R r i

theorem map_rootMatrix {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (r : ℕ) (neg : Bool) (i : Fin r) :
    f.mapMatrix (rootMatrix R r neg i)=rootMatrix S r neg i := by
  cases neg <;> simp only [rootMatrix,Bool.false_eq_true,if_false,if_true,map_positive,map_negative]

theorem rootMatrix_sq_zero (R : Type*) [CommRing R] (r : ℕ) (neg : Bool) (i : Fin r) :
    rootMatrix R r neg i*rootMatrix R r neg i=0 := by
  cases neg
  · simpa only [rootMatrix,Bool.false_eq_true,if_false,pow_two] using positive_sq_zero R r i
  · simpa only [rootMatrix,if_true,pow_two] using negative_sq_zero R r i

def rootTransvection (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) : (Mat K r)ˣ where
  val := 1+t • rootMatrix K r neg i
  inv := 1-t • rootMatrix K r neg i
  val_inv := CFSGSquareZeroConjugation.transvection_mul_inverse t _ (rootMatrix_sq_zero K r neg i)
  inv_val := CFSGSquareZeroConjugation.inverse_mul_transvection t _ (rootMatrix_sq_zero K r neg i)

@[simp] theorem rootTransvection_val (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    (rootTransvection K r neg i t : Mat K r)=1+t • rootMatrix K r neg i := rfl

@[simp] theorem rootTransvection_inv_val (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    (↑((rootTransvection K r neg i t)⁻¹) : Mat K r)=1-t • rootMatrix K r neg i := rfl

def elementaryRootGroup (K : Type*) [CommRing K] (r : ℕ) : Subgroup ((Mat K r)ˣ) :=
  Subgroup.closure {u | ∃neg i t,u=rootTransvection K r neg i t}

theorem rootTransvection_mem (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) : rootTransvection K r neg i t∈elementaryRootGroup K r :=
  Subgroup.subset_closure ⟨neg,i,t,rfl⟩

def elementaryProjective (K : Type*) [CommRing K] (r : ℕ) :=
  (elementaryRootGroup K r) ⧸ Subgroup.center (elementaryRootGroup K r)

instance elementaryProjective_group (K : Type*) [CommRing K] (r : ℕ) :
    Group (elementaryProjective K r) := inferInstanceAs
      (Group ((elementaryRootGroup K r) ⧸ Subgroup.center (elementaryRootGroup K r)))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
