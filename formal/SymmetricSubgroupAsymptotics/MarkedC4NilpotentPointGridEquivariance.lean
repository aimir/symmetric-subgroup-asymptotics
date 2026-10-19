import SymmetricSubgroupAsymptotics.MarkedC4NilpotentPermutationGrid
import SymmetricSubgroupAsymptotics.MarkedC4CoprimeGridEquivariance

/-! Equivariance of the ORIGINAL point-set decomposition. The orbit
index stays fixed and the two physical coset coordinates act separately. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentPointGridEquivariance
open NilpotentSylowFactors NilpotentPermutationGrid
variable (G X : Type) [Group G] [Finite G] [Group.IsNilpotent G] [MulAction G X]
abbrev Grid := Σ ω : OrbitIndex G X, BinaryFiber G X ω × OddFiber G X ω

def gridMove (g : Binary G × OddFactor G) (z : Grid G X) : Grid G X :=
  ⟨z.1,(g.1 • z.2.1,g.2 • z.2.2)⟩

/-- Both coordinates are actual cosets of the original point stabilizer. -/
theorem inverse_mk (ω : OrbitIndex G X) (p : Binary G) (o : OddFactor G) :
    (pointGrid G X).symm ⟨ω,(QuotientGroup.mk p,QuotientGroup.mk o)⟩=
      (equiv G).symm (p,o) • ω.out := by
  letI := factorAction G X
  let e := CoprimePhysicalGrid.orbitGrid (factors_coprime G) ω.out
  have h := CoprimeGridEquivariance.grid_apply (factors_coprime G) ω.out p o
  have hs := congrArg e.symm h
  have hv := congrArg Subtype.val hs
  change ((e.symm (e ⟨(p,o) • ω.out,MulAction.mem_orbit ω.out (p,o)⟩)) : X)=
    ((e.symm (QuotientGroup.mk p,QuotientGroup.mk o)) : X) at hv
  rw [e.symm_apply_apply] at hv
  change ((e.symm (QuotientGroup.mk p,QuotientGroup.mk o)) : X)=_
  exact hv.symm

/-- The original group action transports through the point grid without
altering any orbit label or inventing a replacement permutation action. -/
theorem equivariant (g : G) (x : X) :
    pointGrid G X (g • x)=gridMove G X (equiv G g) (pointGrid G X x) := by
  obtain ⟨z,rfl⟩ := (pointGrid G X).symm.surjective x
  rcases z with ⟨ω,a,d⟩
  induction a using Quotient.inductionOn' with | h p =>
    induction d using Quotient.inductionOn' with | h o =>
      apply (pointGrid G X).symm.injective
      rw [(pointGrid G X).symm_apply_apply,(pointGrid G X).apply_symm_apply,inverse_mk]
      change g • ((equiv G).symm (p,o) • ω.out)=
        (pointGrid G X).symm
          ⟨ω,(QuotientGroup.mk ((equiv G g).1*p),
            QuotientGroup.mk ((equiv G g).2*o))⟩
      rw [inverse_mk]
      change g • ((equiv G).symm (p,o) • ω.out)=
        (equiv G).symm ((equiv G g)*(p,o)) • ω.out
      rw [(equiv G).symm.map_mul,(equiv G).symm_apply_apply,mul_smul]
end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentPointGridEquivariance
