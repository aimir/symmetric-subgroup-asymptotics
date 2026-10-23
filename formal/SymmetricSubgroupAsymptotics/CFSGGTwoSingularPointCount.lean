import SymmetricSubgroupAsymptotics.CFSGGTwoAxisCoordinates
import SymmetricSubgroupAsymptotics.CFSGProjectiveZeroCarrierCardinality

/-! The actual singular lines of the natural G2 invariant hyperplane
number less than 3q^5 for q≥3. This is a carrier count; descending the
natural point action to the original model remains a separate kernel
proof. No group order or exceptional recognition formula is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSingularPointCount
open CFSGGTwoAxisCoordinates CFSGOrthogonalDIndexBundledQuadratic
open CFSGProjectiveZeroCarrierCardinality CFSGSplitOddSingularPointCardinality
variable (K : Type) [Field K]

def axisQuadraticForm : QuadraticForm K (axisHyperplane K) :=
  (splitQuadraticForm K 4).comp (axisHyperplane K).subtype

def singularPoints : Set (Projectivization K (axisHyperplane K)) :=
  {p | axisQuadraticForm K p.rep=0}

theorem singularPoints_card_lt [Finite K] (hq : 3≤Nat.card K) :
    Nat.card (singularPoints K)<3*Nat.card K^5 := by
  have hf := projective_carrier_card_mul_units_add_one_le (singularPoints K)
    {v : axisHyperplane K | axisQuadraticForm K v=0} (by simp) (by
      intro p a
      have hp : axisQuadraticForm K p.val.rep=0 := p.property
      change axisQuadraticForm K ((a:K) • p.val.rep)=0
      rw [QuadraticMap.map_smul,hp,smul_zero])
  have hvec : Nat.card {v : axisHyperplane K | axisQuadraticForm K v=0}≤2*Nat.card K^6 :=
    zero_vectors_card_le K
  apply point_card_lt_three_mul_pow (Nat.card K) 5 (Nat.card (singularPoints K)) hq
  calc
    _≤Nat.card {v : axisHyperplane K | axisQuadraticForm K v=0} := hf
    _≤2*Nat.card K^6 := hvec
    _=2*Nat.card K*Nat.card K^5 := by ring

end SymmetricSubgroupAsymptotics.CFSGGTwoSingularPointCount
