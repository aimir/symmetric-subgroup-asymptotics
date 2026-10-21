import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.Index

/-! Outer-automorphism counting after actual inner alignment. A subgroup
of aligned automorphisms surjects onto Out; its retained inner torus
must be charged in the same incidence count before taking a bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOuterCardinalityAlignment
open PrimitiveSocleRawStructure
variable {G : Type} [Group G] [Finite G]

theorem outer_card_mul_le_aligned (S : Subgroup (MulAut G)) (T : Subgroup G)
    (halign : ∀ f : MulAut G, ∃ g : G, MulAut.conj g*f∈S)
    (hTS : ∀ t : T, MulAut.conj (t : G)∈S)
    (hinj : Function.Injective (fun t : T => MulAut.conj (t : G))) :
    Nat.card (Outer G)*Nat.card T ≤ Nat.card S := by
  let out : MulAut G →* Outer G := QuotientGroup.mk' (Inner G)
  have hkill (g : G) : out (MulAut.conj g)=1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨g,rfl⟩
  let f : S →* Outer G := out.comp S.subtype
  have hsurj : Function.Surjective f := by
    intro o
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (Inner G) o
    obtain ⟨g,hg⟩ := halign a
    refine ⟨⟨MulAut.conj g*a,hg⟩,?_⟩
    change out (MulAut.conj g*a)=o
    rw [map_mul,hkill,one_mul]
    exact ha
  let lift : T → f.ker := fun t =>
    ⟨⟨MulAut.conj (t : G),hTS t⟩,hkill (t : G)⟩
  have hlift : Function.Injective lift := by
    intro t u he
    apply hinj
    exact congrArg (fun z : f.ker => (z.val : MulAut G)) he
  have hT : Nat.card T ≤ Nat.card f.ker := Nat.card_le_card_of_injective lift hlift
  have hindex : f.ker.index=Nat.card (Outer G) := by
    change Nat.card (S ⧸ f.ker)=Nat.card (Outer G)
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  have hc := f.ker.card_mul_index
  rw [hindex] at hc
  calc
    Nat.card (Outer G)*Nat.card T ≤ Nat.card (Outer G)*Nat.card f.ker :=
      Nat.mul_le_mul_left _ hT
    _ = Nat.card S := by rw [Nat.mul_comm,hc]

theorem outer_card_le_of_aligned_bound (S : Subgroup (MulAut G)) (T : Subgroup G)
    (halign : ∀ f : MulAut G, ∃ g : G, MulAut.conj g*f∈S)
    (hTS : ∀ t : T, MulAut.conj (t : G)∈S)
    (hinj : Function.Injective (fun t : T => MulAut.conj (t : G)))
    (d : ℕ) (hS : Nat.card S ≤ Nat.card T*d) : Nat.card (Outer G)≤d := by
  have h := (outer_card_mul_le_aligned S T halign hTS hinj).trans hS
  rw [Nat.mul_comm (Nat.card (Outer G))] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.card_pos (α := T))

end SymmetricSubgroupAsymptotics.CFSGOuterCardinalityAlignment
