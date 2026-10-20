import SymmetricSubgroupAsymptotics.PrimePowerPointBlocks
import SymmetricSubgroupAsymptotics.TwoBlockCentralizerProjection

/-! The two halves of an original transitive binary action, obtained from
an actual stabilizer overgroup. All smaller actions remain on original points. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHalfPointBlocks
open PermutationCharacterRankSplit

variable {G X : Type} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] {x₀ : X} {r : ℕ}
    (D : PrimePowerPointBlock (A := G) x₀ 2 r)

def half : SubMulAction D.subgroup X where
  carrier := {x | D.map x = D.base}
  smul_mem' a x hx := by
    change D.map ((a : G) • x) = D.base
    rw [D.map_equivariant, hx]
    change (a : G) • ((1 : G) : G ⧸ D.subgroup) = ((1 : G) : G ⧸ D.subgroup)
    rw [MulAction.Quotient.smul_coe]
    simpa only [smul_eq_mul,mul_one] using
      (QuotientGroup.eq.mpr (by simpa using D.subgroup.inv_mem a.property) :
        ((a : G) : G ⧸ D.subgroup) = ((1 : G) : G ⧸ D.subgroup))

theorem half_card : Nat.card (half D) = 2 ^ r :=
  D.base_fibre_card

theorem swaps (g : G) (hg : g ∉ D.subgroup) (x : half D) :
    g • (x : X) ∈ ((half D)ᶜ : Set X) := by
  intro he
  change D.map (g • (x : X)) = D.base at he
  rw [D.map_equivariant, x.property] at he
  change g • ((1 : G) : G ⧸ D.subgroup) = ((1 : G) : G ⧸ D.subgroup) at he
  rw [MulAction.Quotient.smul_coe] at he
  have he' : (g : G ⧸ D.subgroup) = ((1 : G) : G ⧸ D.subgroup) := by
    simpa only [smul_eq_mul,mul_one] using he
  have hm := QuotientGroup.eq.mp he'
  apply hg
  simpa only [mul_one, D.subgroup.inv_mem_iff] using hm

theorem half_nonempty : ((half D : SubMulAction D.subgroup X) : Set X).Nonempty := by
  exact ⟨x₀, originalTransitiveBlockMap_base x₀ D.subgroup D.contains⟩

include D in
theorem subgroup_index (hdegree : Nat.card X = 2 ^ (r + 1)) : D.subgroup.index = 2 := by
  have hp := D.degree_product
  change 2 ^ r * D.subgroup.index = Nat.card X at hp
  rw [hdegree, pow_succ] at hp
  have hpos : 0 < 2 ^ r := pow_pos (by decide) _
  nlinarith

variable [Finite X]

include D in
theorem complement_card (hdegree : Nat.card X = 2 ^ (r + 1)) :
    Nat.card ↥((half D)ᶜ) = 2 ^ r := by
  have h := card_split (half D)
  rw [half_card D, hdegree, pow_succ] at h
  omega

include D in
theorem complement_nonempty (hdegree : Nat.card X = 2 ^ (r + 1)) :
    (((half D)ᶜ : SubMulAction D.subgroup X) : Set X).Nonempty := by
  have hp : 0 < Nat.card ↥((half D)ᶜ) := by
    rw [complement_card D hdegree]
    exact pow_pos (by decide) _
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp hp).1
  exact ⟨x,x.property⟩

end SymmetricSubgroupAsymptotics.BinaryHalfPointBlocks
