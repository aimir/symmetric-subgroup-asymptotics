import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
import SymmetricSubgroupAsymptotics.CFSGSymplecticSymmetricShearMembership
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual defining-characteristic unipotent and Borel subgroups of
the SAME elementary C model, in its natural isotropic complete flag.
The order is positive0,...,positiveLast,negativeLast,...,negative0. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices

 def flagEquiv (n : ℕ) : Index n ≃ Fin (n + n) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) Fin.revPerm).trans finSumFinEquiv

@[simp] theorem flagEquiv_pos (n : ℕ) (i : Fin n) :
    flagEquiv n (Sum.inl i) = Fin.castAdd n i := rfl

@[simp] theorem flagEquiv_neg (n : ℕ) (i : Fin n) :
    flagEquiv n (Sum.inr i) = Fin.natAdd n (Fin.revPerm i) := rfl

def borel (K : Type) [Field K] (n : ℕ) : Subgroup (elementaryRootGroup K n) :=
  (CFSGMatrixFlagSubgroups.borelUnits (K := K) (flagEquiv n)).comap (elementaryRootGroup K n).subtype

def unipotent (K : Type) [Field K] (n : ℕ) : Subgroup (elementaryRootGroup K n) :=
  (CFSGMatrixFlagSubgroups.unipotentUnits (K := K) (flagEquiv n)).comap (elementaryRootGroup K n).subtype

@[simp] theorem mem_borel (K : Type) [Field K] (n : ℕ) (g : elementaryRootGroup K n) :
    g ∈ borel K n ↔ (g.val : Mat K n).BlockTriangular (flagEquiv n) := Iff.rfl

@[simp] theorem mem_unipotent (K : Type) [Field K] (n : ℕ) (g : elementaryRootGroup K n) :
    g ∈ unipotent K n ↔
      (g.val : Mat K n).BlockTriangular (flagEquiv n) ∧ ∀ i, (g.val : Mat K n) i i = 1 := Iff.rfl

theorem unipotent_le_borel (K : Type) [Field K] (n : ℕ) : unipotent K n ≤ borel K n :=
  fun _ h => h.1

theorem unipotent_isPGroup (K : Type) [Field K] (n p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (unipotent K n) :=
  (CFSGMatrixFlagSubgroups.unipotentUnits_isPGroup (K := K) (flagEquiv n) p).comap_of_injective
    (elementaryRootGroup K n).subtype Subtype.val_injective

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
