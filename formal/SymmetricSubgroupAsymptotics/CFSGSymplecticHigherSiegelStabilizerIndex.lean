import SymmetricSubgroupAsymptotics.CFSGSymplecticHigherSiegelExtension
import SymmetricSubgroupAsymptotics.AbelianSemidirectStabilizerIndex
import SymmetricSubgroupAsymptotics.SymmetricMatrixAnnihilatorTwoFrameIndex
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Quotient.Card
import Lean.Elab.Tactic.Omega

/-! The exact two-frame lower bound for an actual subgroup of the
literal higher-rank Siegel semidirect product. The actual additive
kernel is only a prime-field subspace; its actual projected subgroup
and the exact same-M index factor are derived, never assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHigherSiegelStabilizerIndex

open SymmetricMatrixCongruenceAction SymmetricMatrixQuadraticFunctional
open CFSGSymplecticHigherSiegelEmbedding CFSGSymplecticHigherSiegelExtension
variable (K : Type) [Field K] [CharP K 2] (m : ℕ)

local instance higherSiegelBaseAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

abbrev Siegel := Multiplicative (Space (K := K) (m + 1)) ⋊[congruenceAction K m]
  GeneralLinear (K := K) (m + 1)

def kernelAdditive (M : Subgroup (Siegel K m)) :
    AddSubgroup (Space (K := K) (m + 1)) where
  carrier := {S | Multiplicative.ofAdd S ∈ M.comap SemidirectProduct.inl}
  zero_mem' := (M.comap SemidirectProduct.inl).one_mem
  add_mem' := fun hS hT => (M.comap SemidirectProduct.inl).mul_mem hS hT
  neg_mem' := fun hS => (M.comap SemidirectProduct.inl).inv_mem hS

/-- Only genuine prime-field linearity of the actual kernel is used. -/
def kernelSubmodule (M : Subgroup (Siegel K m)) :
    Submodule (ZMod 2) (Space (K := K) (m + 1)) :=
  AddSubgroup.toZModSubmodule 2 (kernelAdditive K m M)

theorem quotient_card_eq_kernel_index [Finite K] (M : Subgroup (Siegel K m)) :
    Nat.card (Space (K := K) (m + 1) ⧸ kernelSubmodule K m M) =
      (M.comap SemidirectProduct.inl).index := by
  let J := kernelSubmodule K m M
  let U := M.comap
    (SemidirectProduct.inl : Multiplicative (Space (K := K) (m + 1)) →* Siegel K m)
  have hJ : Nat.card J = Nat.card U := rfl
  have hN : Nat.card (Multiplicative (Space (K := K) (m + 1))) =
      Nat.card (Space (K := K) (m + 1)) := Nat.card_congr Multiplicative.toAdd
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := J))
  calc
    Nat.card J * Nat.card (Space (K := K) (m + 1) ⧸ J) =
        Nat.card (Space (K := K) (m + 1)) := (Submodule.card_eq_card_quotient_mul_card J).symm
    _ = Nat.card U * U.index := hN.symm.trans U.card_mul_index.symm
    _ = Nat.card J * U.index := by rw [hJ]

/-- No independent stabilizer bound occurs: J and L both belong to M. -/
theorem two_frame_le_twice_index [Finite K] (hm : 0 < m)
    (M : Subgroup (Siegel K m)) (i j : Fin (m + 1)) (t : K)
    (ht : SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K m i j t)) ∉ M) :
    (Nat.card K - 1) * Nat.card K ^ (m - 1) *
      (Nat.card K ^ (m + 1) - Nat.card K) ≤ 2 * M.index := by
  let J := kernelSubmodule K m M
  let L := M.map SemidirectProduct.rightHom
  have hJ : ∀ A ∈ L, ∀ S ∈ J, congruenceLinearMap (m + 1) A S ∈ J := by
    intro A hA S hS
    change Multiplicative.ofAdd S ∈ M.comap SemidirectProduct.inl at hS
    change congruenceAction K m A (Multiplicative.ofAdd S) ∈
      M.comap SemidirectProduct.inl
    exact AbelianSemidirectStabilizerIndex.action_mem_kernel_of_projected
      (congruenceAction K m) M A hA (Multiplicative.ofAdd S) hS
  have hnot : t • cross (m + 1) (Pi.single i (1 : K)) (Pi.single j (1 : K)) ∉ J := ht
  have hb := SymmetricMatrixAnnihilatorTwoFrameIndex.two_frame_le_twice_quotient_card_mul_index
    (F := ZMod 2) (m + 1) (by omega) L J hJ (Pi.single i 1) (Pi.single j 1) t hnot
  have hc : Nat.card (Space (K := K) (m + 1) ⧸ J) =
      (M.comap SemidirectProduct.inl).index := quotient_card_eq_kernel_index K m M
  rw [hc] at hb
  have hfac := congrArg (fun n : ℕ => 2 * n)
    (AbelianSemidirectStabilizerIndex.index_factor (congruenceAction K m) M).symm
  have he : m + 1 - 2 = m - 1 := by omega
  simpa only [he] using hb.trans_eq hfac

/-- The actual point stabilizer of the supplied action supplies M. -/
theorem degree_bound_of_offDiagonal_motion [Finite K] (hm : 0 < m)
    {X : Type*} [Finite X] [MulAction (Siegel K m) X]
    (x : X) (i j : Fin (m + 1)) (t : K)
    (hx : (SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K m i j t)) :
      Siegel K m) • x ≠ x) :
    (Nat.card K - 1) * Nat.card K ^ (m - 1) *
      (Nat.card K ^ (m + 1) - Nat.card K) ≤ 2 * Nat.card X := by
  let M := MulAction.stabilizer (Siegel K m) x
  have ht : (SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K m i j t)) :
      Siegel K m) ∉ M := hx
  have hb := two_frame_le_twice_index K m hm M i j t ht
  have ho : M.index = Nat.card (MulAction.orbit (Siegel K m) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (Siegel K m) x)).symm
  rw [ho] at hb
  exact hb.trans (Nat.mul_le_mul_left 2 (Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (Siegel K m) x => y.val) Subtype.val_injective))

end SymmetricSubgroupAsymptotics.CFSGSymplecticHigherSiegelStabilizerIndex
