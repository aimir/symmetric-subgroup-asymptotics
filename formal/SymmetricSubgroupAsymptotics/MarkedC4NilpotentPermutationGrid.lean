import SymmetricSubgroupAsymptotics.MarkedC4NilpotentSylowFactors

/-! The original finite permutation set is partitioned into actual coprime
orbit grids. Summed active binary/odd support fits inside its original
physical degree. No grid chart or physical budget is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentPermutationGrid
open NilpotentSylowFactors

variable (G X : Type) [Group G] [Finite G] [Group.IsNilpotent G] [MulAction G X]
abbrev Factors := Binary G × OddFactor G

def factorAction : MulAction (Factors G) X :=
  MulAction.compHom X (equiv G).symm.toMonoidHom

abbrev OrbitIndex :=
  letI := factorAction G X
  Quotient (MulAction.orbitRel (Factors G) X)

def binaryStabilizer (ω : OrbitIndex G X) : Subgroup (Binary G) := by
  letI := factorAction G X
  exact (MulAction.stabilizer (Factors G) ω.out).map (MonoidHom.fst _ _)

def oddStabilizer (ω : OrbitIndex G X) : Subgroup (OddFactor G) := by
  letI := factorAction G X
  exact (MulAction.stabilizer (Factors G) ω.out).map (MonoidHom.snd _ _)

abbrev BinaryFiber (ω : OrbitIndex G X) := Binary G ⧸ binaryStabilizer G X ω
abbrev OddFiber (ω : OrbitIndex G X) := OddFactor G ⧸ oddStabilizer G X ω

/-- The original point set, not a substitute action of the same degree,
is bijective to the disjoint union of the actual stabilizer grids. -/
def pointGrid : X ≃ Σ ω : OrbitIndex G X, BinaryFiber G X ω × OddFiber G X ω := by
  letI := factorAction G X
  exact (MulAction.selfEquivSigmaOrbits (Factors G) X).trans
    (Equiv.sigmaCongrRight fun ω => CoprimePhysicalGrid.orbitGrid (factors_coprime G) ω.out)

variable [Finite X]
local instance : Fintype (OrbitIndex G X) := Fintype.ofFinite _

def binaryDegree : ℕ := ∑ ω : OrbitIndex G X,
  CoprimePhysicalGrid.activeDegree (Nat.card (BinaryFiber G X ω))
def oddDegree : ℕ := ∑ ω : OrbitIndex G X,
  CoprimePhysicalGrid.activeDegree (Nat.card (OddFiber G X ω))

/-- A single exact physical budget controls both prime parts. -/
theorem support_budget : binaryDegree G X+oddDegree G X≤Nat.card X := by
  rw [Nat.card_congr (pointGrid G X),Nat.card_sigma]
  simp_rw [Nat.card_prod]
  unfold binaryDegree oddDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  exact CoprimePhysicalGrid.activeDegree_budget Nat.card_pos Nat.card_pos

end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentPermutationGrid
