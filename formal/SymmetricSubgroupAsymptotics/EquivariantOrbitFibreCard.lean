import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-! An orbit in an actual equivariant block map contains a product of its
block orbit with any subgroup orbit in one original fibre. The injection
uses chosen transporters, so no splitting, complement, or full base group
is required. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G X I : Type} [Group G] [MulAction G X] [MulAction G I]
    (b : X → I) (hb : ∀ (g : G) (x : X), b (g • x) = g • b x)
    (K : Subgroup G) (x : X)

private def orbitTransporter (y : MulAction.orbit G (b x)) : G :=
  Classical.choose (MulAction.mem_orbit_iff.mp y.2)

private theorem orbitTransporter_spec (y : MulAction.orbit G (b x)) :
    orbitTransporter b x y • b x = (y : I) :=
  Classical.choose_spec (MulAction.mem_orbit_iff.mp y.2)

/-- This is an injection into the original orbit, not merely an order
comparison in a quotient group. -/
def orbitFibreInjection : MulAction.orbit G (b x) × MulAction.orbit K x →
    MulAction.orbit G x := fun yz =>
  ⟨orbitTransporter b x yz.1 • (yz.2 : X),
    MulAction.mem_orbit_of_mem_orbit _
      (MulAction.mem_orbit_of_mem_orbit_subgroup yz.2.2)⟩

include hb in
theorem orbitFibreInjection_injective
    (hK : ∀ k : K, (k : G) • b x = b x) :
    Function.Injective (orbitFibreInjection b K x) := by
  have hz (z : MulAction.orbit K x) : b (z : X) = b x := by
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp z.2
    rw [← hk]
    exact (hb k x).trans (hK k)
  rintro ⟨i, z⟩ ⟨j, w⟩ hij
  have he : orbitTransporter b x i • (z : X) =
      orbitTransporter b x j • (w : X) := congrArg Subtype.val hij
  have hbase := congrArg b he
  rw [hb, hb, hz, hz, orbitTransporter_spec, orbitTransporter_spec] at hbase
  have hi : i = j := Subtype.ext hbase
  subst j
  have hw : z = w := Subtype.ext ((MulAction.injective (orbitTransporter b x i)) he)
  subst w
  rfl

include hb in
/-- Orbit sizes multiply as a lower bound with the actual stabilizing
subgroup and the exact block orbit, even for correlated kernels. -/
theorem orbit_card_ge_block_mul_fibre [Finite X] [Finite I]
    (hK : ∀ k : K, (k : G) • b x = b x) :
    Nat.card (MulAction.orbit G (b x)) * Nat.card (MulAction.orbit K x) ≤
      Nat.card (MulAction.orbit G x) := by
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective
    (orbitFibreInjection b K x) (orbitFibreInjection_injective b hb K x hK)

end SymmetricSubgroupAsymptotics

end
