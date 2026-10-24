import SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalExtension
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllNormOrbitCardinality
import SymmetricSubgroupAsymptotics.NondegenerateBilinearAnnihilatorOrbitIndex
import SymmetricSubgroupAsymptotics.AbelianSemidirectStabilizerIndex
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.Quotient.Card

/-! One subgroup of the actual twisted-D point semidirect product
supplies BOTH its additive kernel and projected relative subgroup. The
kernel is only prime-field linear; the preserved natural polar form
transfers its genuine annihilator orbit to the actual natural orbit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalStabilizerIndex

open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedQuadraticNondegenerate CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDPointRadicalExtension CFSGTwistedDAllNormOrbitCardinality
open CFSGTwistedA2FixedField

local instance primeAlgebra (p : ℕ) (q : CFSG.PrimePower)
    [Fact p.Prime] [CharP (fixedField q) p] : Algebra (ZMod p) (fixedField q) :=
  ZMod.algebra (fixedField q) p

local instance primeModule (p : ℕ) (q : CFSG.PrimePower) (n : ℕ)
    [Fact p.Prime] [CharP (fixedField q) p] : Module (ZMod p) (fixedSpace n q) :=
  Module.restrictScalars (ZMod p) (fixedField q) (fixedSpace n q)

local instance primeTower (p : ℕ) (q : CFSG.PrimePower) (n : ℕ)
    [Fact p.Prime] [CharP (fixedField q) p] : IsScalarTower (ZMod p) (fixedField q) (fixedSpace n q) :=
  IsScalarTower.restrictScalars (ZMod p) (fixedField q) (fixedSpace n q)

abbrev PointParabolic (n : ℕ) (q : CFSG.PrimePower) :=
  Multiplicative (fixedSpace (n + 1) q) ⋊[tailAction (n + 1) q] relativeRootGroup (n + 1) q

def kernelAdditive (n : ℕ) (q : CFSG.PrimePower) (M : Subgroup (PointParabolic n q)) :
    AddSubgroup (fixedSpace (n + 1) q) where
  carrier := {v | Multiplicative.ofAdd v ∈ M.comap SemidirectProduct.inl}
  zero_mem' := (M.comap SemidirectProduct.inl).one_mem
  add_mem' := fun hv hw => (M.comap SemidirectProduct.inl).mul_mem hv hw
  neg_mem' := fun hv => (M.comap SemidirectProduct.inl).inv_mem hv

def kernelSubmodule (n : ℕ) (q : CFSG.PrimePower)
    (p : ℕ) [Fact p.Prime] [CharP (fixedField q) p]
    (M : Subgroup (PointParabolic n q)) : Submodule (ZMod p) (fixedSpace (n + 1) q) :=
  AddSubgroup.toZModSubmodule p (kernelAdditive n q M)

theorem quotient_card_eq_kernel_index (n : ℕ) (q : CFSG.PrimePower)
    (p : ℕ) [Fact p.Prime] [CharP (fixedField q) p] (M : Subgroup (PointParabolic n q)) :
    Nat.card (fixedSpace (n + 1) q ⧸ kernelSubmodule n q p M) =
      (M.comap SemidirectProduct.inl).index := by
  let J := kernelSubmodule n q p M
  let U := M.comap (SemidirectProduct.inl : Multiplicative (fixedSpace (n + 1) q) →* PointParabolic n q)
  have hJ : Nat.card J = Nat.card U := rfl
  have hN : Nat.card (Multiplicative (fixedSpace (n + 1) q)) = Nat.card (fixedSpace (n + 1) q) :=
    Nat.card_congr Multiplicative.toAdd
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := J))
  calc
    Nat.card J * Nat.card (fixedSpace (n + 1) q ⧸ J) = Nat.card (fixedSpace (n + 1) q) :=
      (Submodule.card_eq_card_quotient_mul_card J).symm
    _ = Nat.card U * U.index := hN.symm.trans U.card_mul_index.symm
    _ = Nat.card J * U.index := by rw [hJ]

theorem natural_slice_le_index (n : ℕ) (q : CFSG.PrimePower)
    (p : ℕ) [Fact p.Prime] [CharP (fixedField q) p]
    (M : Subgroup (PointParabolic n q)) (z : fixedSpace (n + 1) q)
    (hz : SemidirectProduct.inl (Multiplicative.ofAdd z) ∉ M) :
    (q.order ^ (n + 2) - 1) * q.order ^ (n + 3) ≤ M.index := by
  let J := kernelSubmodule n q p M
  let L := M.map SemidirectProduct.rightHom
  let ρ := fixedLinearHom (n + 1) q
  let Q := fixedQuadraticForm (n + 1) q
  have hJ : ∀ g ∈ L, ∀ v ∈ J,
      FiniteFieldFunctionalOrbitTransfer.restrictedRepresentation (F := ZMod p) ρ g v ∈ J := by
    intro g hg v hv
    change Multiplicative.ofAdd v ∈ M.comap SemidirectProduct.inl at hv
    change tailAction (n + 1) q g (Multiplicative.ofAdd v) ∈ M.comap SemidirectProduct.inl
    exact AbelianSemidirectStabilizerIndex.action_mem_kernel_of_projected
      (tailAction (n + 1) q) M g hg (Multiplicative.ofAdd v) hv
  have hρ : ∀ g : relativeRootGroup (n + 1) q, ∀ v w : fixedSpace (n + 1) q,
      Q.polarBilin (ρ g v) (ρ g w) = Q.polarBilin v w := by
    intro g v w
    exact QuadraticHyperbolicRadicalHom.polar_preserved Q (ρ g)
      (fixedLinearHom_preserves_Q (n + 1) q g) v w
  have hlow := NondegenerateBilinearAnnihilatorOrbitIndex.natural_orbit_lower_le_quotient_card_mul_index
    Q.polarBilin (fixedQuadraticForm_nondegenerate (n + 1) q) ρ hρ
    ((q.order ^ (n + 2) - 1) * q.order ^ (n + 3))
    (fun v hv => norm_slice_le_vectorOrbit n q v hv) L J hJ z hz
  rw [quotient_card_eq_kernel_index n q p M] at hlow
  exact hlow.trans_eq (AbelianSemidirectStabilizerIndex.index_factor (tailAction (n + 1) q) M).symm

theorem degree_bound_of_radical_motion (n : ℕ) (q : CFSG.PrimePower)
    (p : ℕ) [Fact p.Prime] [CharP (fixedField q) p]
    {X : Type*} [Finite X] [MulAction (PointParabolic n q) X]
    (x : X) (z : fixedSpace (n + 1) q)
    (hx : (SemidirectProduct.inl (Multiplicative.ofAdd z) : PointParabolic n q) • x ≠ x) :
    (q.order ^ (n + 2) - 1) * q.order ^ (n + 3) ≤ Nat.card X := by
  let M := MulAction.stabilizer (PointParabolic n q) x
  have hz : (SemidirectProduct.inl (Multiplicative.ofAdd z) : PointParabolic n q) ∉ M := hx
  have hb := natural_slice_le_index n q p M z hz
  have ho : M.index = Nat.card (MulAction.orbit (PointParabolic n q) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (PointParabolic n q) x)).symm
  rw [ho] at hb
  exact hb.trans (Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (PointParabolic n q) x => y.val) Subtype.val_injective)

end SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalStabilizerIndex
