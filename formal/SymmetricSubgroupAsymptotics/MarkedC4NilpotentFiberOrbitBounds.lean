import SymmetricSubgroupAsymptotics.MarkedC4NilpotentPermutationGrid
import SymmetricSubgroupAsymptotics.MarkedC4ActiveFiberOrbitBounds

/-! Actual original orbit bounds dominate both compressed physical fibers.
The factor action has the SAME point orbits, proved by its group equivalence. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentFiberOrbitBounds
open NilpotentSylowFactors NilpotentPermutationGrid
variable (G X : Type) [Group G] [Finite G] [Group.IsNilpotent G] [MulAction G X]

def orbitEquiv (x : X) :
    letI := factorAction G X
    MulAction.orbit G x ≃ MulAction.orbit (Factors G) x := by
  letI := factorAction G X
  refine
    { toFun := fun z => ⟨z.1,?_⟩
      invFun := fun z => ⟨z.1,?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · obtain ⟨g,hg⟩ := z.property
    refine ⟨equiv G g,?_⟩
    change (equiv G).symm (equiv G g) • x=z.1
    simpa only [MulEquiv.symm_apply_apply] using hg
  · obtain ⟨g,hg⟩ := z.property
    exact ⟨(equiv G).symm g,hg⟩

theorem orbit_card (ω : OrbitIndex G X) :
    Nat.card (MulAction.orbit G ω.out)=
      Nat.card (BinaryFiber G X ω)*Nat.card (OddFiber G X ω) := by
  letI := factorAction G X
  rw [Nat.card_congr (orbitEquiv G X ω.out)]
  exact CoprimePhysicalGrid.orbit_card (factors_coprime G) ω.out

theorem binary_fiber_le (ω : OrbitIndex G X) :
    Nat.card (BinaryFiber G X ω)≤Nat.card (MulAction.orbit G ω.out) := by
  rw [orbit_card G X ω]
  have hd : 1≤Nat.card (OddFiber G X ω) := Nat.card_pos
  simpa only [mul_one] using Nat.mul_le_mul_left (Nat.card (BinaryFiber G X ω)) hd

theorem odd_fiber_le (ω : OrbitIndex G X) :
    Nat.card (OddFiber G X ω)≤Nat.card (MulAction.orbit G ω.out) := by
  rw [orbit_card G X ω]
  have ha : 1≤Nat.card (BinaryFiber G X ω) := Nat.card_pos
  simpa only [one_mul] using Nat.mul_le_mul_right (Nat.card (OddFiber G X ω)) ha

theorem fiber_cutoff {C : ℕ} (hC : ∀ x : X,Nat.card (MulAction.orbit G x)<C) :
    (∀ ω : OrbitIndex G X,Nat.card (BinaryFiber G X ω)<C) ∧
    (∀ ω : OrbitIndex G X,Nat.card (OddFiber G X ω)<C) :=
  ⟨fun ω => (binary_fiber_le G X ω).trans_lt (hC ω.out),
   fun ω => (odd_fiber_le G X ω).trans_lt (hC ω.out)⟩
end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentFiberOrbitBounds
