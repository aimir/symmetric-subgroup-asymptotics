import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerLieLeibniz
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice

/-! The original least divided-power-stable integral Serre lattice is
closed under its genuine rational Lie bracket. No finite-type basis,
matrix recognition or characteristic restriction is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreIntegralLieClosure
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreLocalNilpotence
open CFSGSerreDividedPowers CFSGSerreDividedPowerLieLeibniz
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

def bracketStabilizer : LieSubalgebra ℤ (RationalLie A) where
  carrier := {x | ∀ y ∈ integralLattice A, ⁅x,y⁆ ∈ integralLattice A}
  zero_mem' := by intro y hy; simpa only [zero_lie] using (integralLattice A).zero_mem
  add_mem' := by
    intro x y hx hy z hz
    rw [add_lie]
    exact (integralLattice A).add_mem (hx z hz) (hy z hz)
  smul_mem' := by
    intro a x hx y hy
    rw [smul_lie]
    exact (integralLattice A).smul_mem a (hx y hy)
  lie_mem' := by
    intro x y hx hy z hz
    rw [lie_lie]
    exact (integralLattice A).sub_mem (hx _ (hy z hz)) (hy _ (hx z hz))

theorem dividedPower_stabilizes (negative : Bool) (i : Fin r)
    (x : RationalLie A) (hx : x ∈ bracketStabilizer A) (k : ℕ) :
    dividedPower A negative i k x ∈ bracketStabilizer A := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro y hy
    have he := dividedPower_lie A negative i k x y
    rw [Finset.sum_range_succ] at he
    simp only [Nat.sub_self, dividedPower_zero, Module.End.one_apply] at he
    have hsum : (∑ j ∈ Finset.range k,
        ⁅dividedPower A negative i j x, dividedPower A negative i (k-j) y⁆)
          ∈ integralLattice A := by
      apply (integralLattice A).sum_mem
      intro j hj
      exact ih j (Finset.mem_range.mp hj) _
        (dividedPower_mem A negative i (k-j) y hy)
    have hwhole := dividedPower_mem A negative i k ⁅x,y⁆ (hx y hy)
    have hz : ⁅dividedPower A negative i k x,y⁆ =
        dividedPower A negative i k ⁅x,y⁆ -
          ∑ j ∈ Finset.range k,
            ⁅dividedPower A negative i j x, dividedPower A negative i (k-j) y⁆ := by
      rw [he]
      abel
    rw [hz]
    exact (integralLattice A).sub_mem hwhole hsum

theorem rootVector_stabilizes (negative : Bool) (i : Fin r) :
    rootVector A negative i ∈ bracketStabilizer A := by
  intro y hy
  have h := dividedPower_mem A negative i 1 y hy
  simpa only [dividedPower, Nat.factorial_one, Nat.cast_one, inv_one,
    one_smul, pow_one, LinearMap.restrictScalars_apply, LieAlgebra.ad_apply] using h

theorem lie_mem (x y : RationalLie A) (hx : x ∈ integralLattice A)
    (hy : y ∈ integralLattice A) : ⁅x,y⁆ ∈ integralLattice A := by
  have hs : integralLattice A ≤ (bracketStabilizer A).toSubmodule := by
    apply integralLattice_le_of_stable
    · intro g
      cases g with
      | E i => exact rootVector_stabilizes A false i
      | F i => exact rootVector_stabilizes A true i
      | H i =>
        rw [← generator_EF_same A i]
        exact (bracketStabilizer A).lie_mem
          (rootVector_stabilizes A false i) (rootVector_stabilizes A true i)
    · intro negative i k z hz
      exact dividedPower_stabilizes A negative i z hz k
  exact hs hx y hy

def integralLieSubalgebra : LieSubalgebra ℤ (RationalLie A) where
  __ := integralLattice A
  lie_mem' := fun {x y} hx hy => lie_mem A x y hx hy

end SymmetricSubgroupAsymptotics.CFSGSerreIntegralLieClosure
