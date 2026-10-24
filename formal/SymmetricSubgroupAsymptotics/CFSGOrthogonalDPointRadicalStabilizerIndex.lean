import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalExtension
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllNormOrbitCardinality
import SymmetricSubgroupAsymptotics.NondegenerateBilinearAnnihilatorOrbitIndex
import SymmetricSubgroupAsymptotics.AbelianSemidirectStabilizerIndex
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Quotient.Card

/-! The actual kernel J and actual projected subgroup L of one subgroup
M of the literal D point semidirect product pay the natural-orbit bound.
J is only a prime-field subspace, never a larger-field subspace. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalStabilizerIndex

open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDPointRadicalExtension
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDPointRadicalNormalizer CFSGOrthogonalDAllNormOrbitCardinality
variable (K : Type) [Field K]

local instance pointRadicalPrimeAlgebra (p : ℕ) [Fact p.Prime] [CharP K p] :
    Algebra (ZMod p) K := ZMod.algebra K p

abbrev PointParabolic (s : ℕ) := Multiplicative (Index (s + 2) → K) ⋊[tailAction K s]
  elementaryRootGroup K (s + 2)

def kernelAdditive (s : ℕ) (M : Subgroup (PointParabolic K s)) :
    AddSubgroup (Index (s + 2) → K) where
  carrier := {v | Multiplicative.ofAdd v ∈ M.comap SemidirectProduct.inl}
  zero_mem' := (M.comap SemidirectProduct.inl).one_mem
  add_mem' := fun hv hw => (M.comap SemidirectProduct.inl).mul_mem hv hw
  neg_mem' := fun hv => (M.comap SemidirectProduct.inl).inv_mem hv

def kernelSubmodule (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) (M : Subgroup (PointParabolic K s)) :
    Submodule (ZMod p) (Index (s + 2) → K) :=
  AddSubgroup.toZModSubmodule p (kernelAdditive K s M)

theorem quotient_card_eq_kernel_index [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ) (M : Subgroup (PointParabolic K s)) :
    Nat.card ((Index (s + 2) → K) ⧸ kernelSubmodule K p s M) =
      (M.comap SemidirectProduct.inl).index := by
  let J := kernelSubmodule K p s M
  let U := M.comap
    (SemidirectProduct.inl : Multiplicative (Index (s + 2) → K) →* PointParabolic K s)
  have hJ : Nat.card J = Nat.card U := rfl
  have hN : Nat.card (Multiplicative (Index (s + 2) → K)) =
      Nat.card (Index (s + 2) → K) := Nat.card_congr Multiplicative.toAdd
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := J))
  calc
    Nat.card J * Nat.card ((Index (s + 2) → K) ⧸ J) =
        Nat.card (Index (s + 2) → K) := (Submodule.card_eq_card_quotient_mul_card J).symm
    _ = Nat.card U * U.index := hN.symm.trans U.card_mul_index.symm
    _ = Nat.card J * U.index := by rw [hJ]

theorem natural_slice_le_index [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (M : Subgroup (PointParabolic K s)) (z : Index (s + 2) → K)
    (hz : SemidirectProduct.inl (Multiplicative.ofAdd z) ∉ M) :
    (Nat.card K ^ (s + 2) - 1) * Nat.card K ^ (s + 1) ≤ M.index := by
  let J := kernelSubmodule K p s M
  let L := M.map SemidirectProduct.rightHom
  let ρ := naturalLinearHom K (s + 2)
  let Q := splitQuadraticForm K (s + 2)
  have hJ : ∀ g ∈ L, ∀ v ∈ J,
      FiniteFieldFunctionalOrbitTransfer.restrictedRepresentation (F := ZMod p) ρ g v ∈ J := by
    intro g hg v hv
    change Multiplicative.ofAdd v ∈ M.comap SemidirectProduct.inl at hv
    change tailAction K s g (Multiplicative.ofAdd v) ∈ M.comap SemidirectProduct.inl
    exact AbelianSemidirectStabilizerIndex.action_mem_kernel_of_projected
      (tailAction K s) M g hg (Multiplicative.ofAdd v) hv
  have hρ : ∀ g : elementaryRootGroup K (s + 2), ∀ v w : Index (s + 2) → K,
      Q.polarBilin (ρ g v) (ρ g w) = Q.polarBilin v w := by
    intro g v w
    exact QuadraticHyperbolicRadicalHom.polar_preserved Q (ρ g)
      (tail_preserves_quadratic K s g) v w
  have hlow := NondegenerateBilinearAnnihilatorOrbitIndex.natural_orbit_lower_le_quotient_card_mul_index
    Q.polarBilin (splitQuadraticForm_nondegenerate K (s + 2)) ρ hρ
    ((Nat.card K ^ (s + 2) - 1) * Nat.card K ^ (s + 1))
    (fun v hv => norm_slice_le_vectorOrbit K s v hv) L J hJ z hz
  rw [quotient_card_eq_kernel_index K p s M] at hlow
  exact hlow.trans_eq (AbelianSemidirectStabilizerIndex.index_factor (tailAction K s) M).symm

theorem degree_bound_of_radical_motion [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    {X : Type*} [Finite X] [MulAction (PointParabolic K s) X]
    (x : X) (z : Index (s + 2) → K)
    (hx : (SemidirectProduct.inl (Multiplicative.ofAdd z) : PointParabolic K s) • x ≠ x) :
    (Nat.card K ^ (s + 2) - 1) * Nat.card K ^ (s + 1) ≤ Nat.card X := by
  let M := MulAction.stabilizer (PointParabolic K s) x
  have hz : (SemidirectProduct.inl (Multiplicative.ofAdd z) : PointParabolic K s) ∉ M := hx
  have hb := natural_slice_le_index K p s M z hz
  have ho : M.index = Nat.card (MulAction.orbit (PointParabolic K s) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (PointParabolic K s) x)).symm
  rw [ho] at hb
  exact hb.trans (Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (PointParabolic K s) x => y.val) Subtype.val_injective)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalStabilizerIndex
