import SymmetricSubgroupAsymptotics.InducedNormalCoreCyclicOrbitCapacity
import SymmetricSubgroupAsymptotics.InducedDoubleCosetIndices

/-! A normal coefficient core, cyclic top, and one actual derangement give
a half-degree generator bound for every original induced subrepresentation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

variable {k G I V : Type} [Field k] [Finite k] [Group G] [Finite G]
    [Finite I] [MulAction G I] [MulAction.IsPretransitive G I]
    [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V] [FiniteDimensional k V]

/-- All hypotheses concern the literal acting group and local coefficient
representation. No Tracey theorem, Hall subgroup, or orbit-width estimate
is assumed. -/
theorem induced_normalCore_derangement_uniform_half
    (i : I) (N B : Subgroup G) [B.Normal]
    (hBH : B≤MulAction.stabilizer G i) (hBN : B≤N)
    [IsCyclic (N⧸B.subgroupOf N)]
    (rho : Representation k (MulAction.stabilizer G i) V)
    (hchi : Nat.card (Quotient (representationNonzeroOrbitRel
      (Representation.dual (rho.comp (B.subgroupOf (MulAction.stabilizer G i)).subtype))))=1)
    (z : N) (hz : ∀ x : I,z • x≠x) :
    UniformSubrepresentationGeneratorBound
      (Representation.ind (MulAction.stabilizer G i).subtype rho) (Nat.card I/2) := by
  let H := MulAction.stabilizer G i
  let Q := DoubleCoset.Quotient (H : Set G) (N : Set G)
  letI : Finite Q := Finite.of_injective (inducedDoubleCosetOrbitEquiv H N)
    (inducedDoubleCosetOrbitEquiv H N).injective
  letI : Fintype Q := Fintype.ofFinite _
  have hsize (q : Q) : 2≤(inducedOrbitStabilizer H N q.out).index := by
    apply Subgroup.one_lt_index_of_ne_top
    intro ht
    have hmem : z∈inducedOrbitStabilizer H N q.out := by rw [ht]; exact Subgroup.mem_top z
    have hfix : (q.out*(z : G)*q.out⁻¹) • i=i := hmem
    have h := congrArg (fun x : I => q.out⁻¹ • x) hfix
    have hzfix : z • (q.out⁻¹ • i)=q.out⁻¹ • i := by
      simpa only [mul_smul,inv_smul_smul] using h
    exact hz _ hzfix
  have hcount : Fintype.card Q≤H.index/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    calc
      Fintype.card Q*2=∑ _q : Q,2 := by simp
      _ ≤ ∑ q : Q,(inducedOrbitStabilizer H N q.out).index :=
        Finset.sum_le_sum (fun q _ => hsize q)
      _ = H.index := inducedMackey_index_sum H N
  have hgen := induced_normalCore_cyclic_orbit_uniform H N B hBH hBN rho hchi
  apply hgen.mono
  simpa only [H,MulAction.index_stabilizer_of_transitive] using hcount

end SymmetricSubgroupAsymptotics
