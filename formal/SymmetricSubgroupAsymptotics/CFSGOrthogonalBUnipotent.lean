import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryGroup
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal B unipotent and Borel subgroups of the SAME natural root
matrix group. The actual complete flag orders positive coordinates,
then the middle coordinate, then negative coordinates in reverse. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices

def tailEquiv (n : ℕ) : Fin n ⊕ Unit ≃ Fin (1 + n) :=
  (Equiv.sumComm (Fin n) Unit).trans
    ((Equiv.sumCongr (Equiv.ofUnique Unit (Fin 1)) Fin.revPerm).trans finSumFinEquiv)

def flagEquiv (n : ℕ) : Index n ≃ Fin (n + (1 + n)) :=
  (Equiv.sumAssoc (Fin n) (Fin n) Unit).trans
    ((Equiv.sumCongr (Equiv.refl (Fin n)) (tailEquiv n)).trans finSumFinEquiv)

@[simp] theorem flagEquiv_pos (n : ℕ) (i : Fin n) :
    flagEquiv n (pos n i) = Fin.castAdd (1 + n) i := rfl

@[simp] theorem flagEquiv_middle (n : ℕ) :
    flagEquiv n (middle n) = Fin.natAdd n (Fin.castAdd n (0 : Fin 1)) := rfl

@[simp] theorem flagEquiv_neg (n : ℕ) (i : Fin n) :
    flagEquiv n (neg n i) = Fin.natAdd n (Fin.natAdd 1 (Fin.revPerm i)) := rfl

theorem flag_pos_lt_middle (n : ℕ) (i : Fin n) :
    flagEquiv n (pos n i) < flagEquiv n (middle n) := by
  change i.val < n
  exact i.isLt

theorem flag_middle_lt_neg (n : ℕ) (i : Fin n) :
    flagEquiv n (middle n) < flagEquiv n (neg n i) := by
  change n < n + (1 + (Fin.rev i).val)
  omega

theorem flag_pos_lt_neg (n : ℕ) (i j : Fin n) :
    flagEquiv n (pos n i) < flagEquiv n (neg n j) :=
  (flag_pos_lt_middle n i).trans (flag_middle_lt_neg n j)

theorem flag_neg_lt_neg (n : ℕ) (i j : Fin n) :
    flagEquiv n (neg n i) < flagEquiv n (neg n j) ↔ j < i := by
  change n + (1 + (Fin.rev i).val) < n + (1 + (Fin.rev j).val) ↔ j.val < i.val
  rw [Nat.add_lt_add_iff_left, Nat.add_lt_add_iff_left]
  exact Fin.rev_lt_rev

def borel (K : Type) [Field K] (n : ℕ) : Subgroup (elementaryRootGroup K n) :=
  (CFSGMatrixFlagSubgroups.borelUnits (K := K) (flagEquiv n)).comap (elementaryRootGroup K n).subtype

def unipotent (K : Type) [Field K] (n : ℕ) : Subgroup (elementaryRootGroup K n) :=
  (CFSGMatrixFlagSubgroups.unipotentUnits (K := K) (flagEquiv n)).comap (elementaryRootGroup K n).subtype

@[simp] theorem mem_borel (K : Type) [Field K] (n : ℕ) (g : elementaryRootGroup K n) :
    g ∈ borel K n ↔ (g.val : Mat K n).BlockTriangular (flagEquiv n) := Iff.rfl

@[simp] theorem mem_unipotent (K : Type) [Field K] (n : ℕ) (g : elementaryRootGroup K n) :
    g ∈ unipotent K n ↔
      (g.val : Mat K n).BlockTriangular (flagEquiv n) ∧ ∀ i, (g.val : Mat K n) i i = 1 := Iff.rfl

theorem unipotent_le_borel (K : Type) [Field K] (n : ℕ) : unipotent K n ≤ borel K n := fun _ h => h.1

theorem unipotent_isPGroup (K : Type) [Field K] (n p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (unipotent K n) :=
  (CFSGMatrixFlagSubgroups.unipotentUnits_isPGroup (K := K) (flagEquiv n) p).comap_of_injective
    (elementaryRootGroup K n).subtype Subtype.val_injective

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
