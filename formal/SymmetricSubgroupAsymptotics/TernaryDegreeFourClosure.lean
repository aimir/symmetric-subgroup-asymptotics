import SymmetricSubgroupAsymptotics.C3EpimorphismCharacters
import SymmetricSubgroupAsymptotics.TernaryDegreeNineClosure
import Mathlib.GroupTheory.Index

/-!
# Structural closure of the degree-four ternary endpoint

A transitive four-point permutation group carrying a rank-one relative
ternary head is the natural alternating group.  A nonzero relative character
forces the group order to be divisible by three, while transitivity forces
divisibility by four.  Lagrange leaves orders twelve and twenty-four.  The
full symmetric group kills every invariant ternary character by conjugating
each permutation to its inverse, so only the natural `A₄` action remains.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem finFour_exists_conjugate_inverse (s : Equiv.Perm (Fin 4)) :
    ∃ g : Equiv.Perm (Fin 4), g * s * g⁻¹ = s⁻¹ := by
  decide +kernel +revert

/-- If a four-point permutation subgroup is the whole symmetric group,
ambient inversion annihilates the relative ternary head of every normal
subgroup. -/
theorem degreeFour_top_relativeHead_eq_zero
    (U : Subgroup (Equiv.Perm (Fin 4))) (hU : U = ⊤)
    (M : Subgroup U) [M.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 0 := by
  letI : Subsingleton (primeRelativeCharacters 3 M) := ⟨by
    intro χ ψ
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro a
    let m : M := a.toMul
    change χ.1 (Additive.ofMul m) = ψ.1 (Additive.ofMul m)
    have character_zero : ∀ θ : primeRelativeCharacters 3 M,
        θ.1 (Additive.ofMul m) = 0 := by
      intro θ
      obtain ⟨g₀, hg₀⟩ :=
        finFour_exists_conjugate_inverse ((m : M) : Equiv.Perm (Fin 4))
      let g : U := ⟨g₀, by rw [hU]; exact Subgroup.mem_top g₀⟩
      have hg : g * (m : U) * g⁻¹ = (m : U)⁻¹ := by
        apply Subtype.ext
        exact hg₀
      have hθ := θ.2 g m
      have hconj :
          (⟨g * (m : U) * g⁻¹,
            Subgroup.Normal.conj_mem inferInstance (m : U) m.2 g⟩ : M) = m⁻¹ := by
        apply Subtype.ext
        exact hg
      rw [hconj] at hθ
      change θ.1 (-Additive.ofMul m) = θ.1 (Additive.ofMul m) at hθ
      rw [map_neg] at hθ
      let x : ZMod 3 := θ.1 (Additive.ofMul m)
      have htwo : (2 : ZMod 3) * x = 0 := by
        calc
          (2 : ZMod 3) * x = x + x := by ring
          _ = x + -x := by rw [hθ]
          _ = 0 := add_neg_cancel x
      exact (mul_eq_zero.mp htwo).resolve_left (by decide)
    rw [character_zero χ, character_zero ψ]⟩
  exact Module.finrank_zero_of_subsingleton

/-- Literal classification of the degree-four endpoint. -/
theorem degreeFourPermutation_rankOne_eq_alternating
    (U : Subgroup (Equiv.Perm (Fin 4)))
    [MulAction.IsPretransitive U (Fin 4)]
    (M : Subgroup U) [M.Normal]
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 1) :
    U = alternatingGroup (Fin 4) := by
  have hrankPos : 0 < Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) := by
    omega
  letI : Nontrivial (primeRelativeCharacters 3 M) :=
    Module.finrank_pos_iff.mp hrankPos
  obtain ⟨θ, hθ⟩ := exists_ne (0 : primeRelativeCharacters 3 M)
  have hθ0 : (θ.1 : PrimeCharacters 3 M) ≠ 0 := by
    intro hz
    apply hθ
    apply Subtype.ext
    exact hz
  have h3M : 3 ∣ Nat.card M := by
    have hd := Subgroup.card_dvd_of_surjective (ternaryCharacterHom θ.1)
      ((ternaryCharacter_surjective_iff_ne_zero θ.1).mpr hθ0)
    simpa only [TernaryCyclic, Nat.card_eq_fintype_card, ZMod.card] using hd
  have h3U : 3 ∣ Nat.card U := h3M.trans M.card_subgroup_dvd_card
  have hindex : (MulAction.stabilizer U (0 : Fin 4)).index = 4 := by
    simpa only [Nat.card_fin] using MulAction.index_stabilizer_of_transitive U (0 : Fin 4)
  have hmul := (MulAction.stabilizer U (0 : Fin 4)).card_mul_index
  rw [hindex] at hmul
  have h4U : 4 ∣ Nat.card U := ⟨Nat.card (MulAction.stabilizer U (0 : Fin 4)), by omega⟩
  have hUle : Nat.card U ≤ 24 := by
    have h := Subgroup.card_le_card_group U
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at h ⊢
    exact h
  have hUpos : 0 < Nat.card U := Nat.card_pos
  rcases h3U with ⟨a, ha⟩
  rcases h4U with ⟨b, hb⟩
  have hcard : Nat.card U = 12 ∨ Nat.card U = 24 := by omega
  rcases hcard with h12 | h24
  · apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have h := U.card_mul_index
    have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    rw [h12, hperm] at h
    omega
  · have htop : U = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [h24]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hzero := degreeFour_top_relativeHead_eq_zero U htop M
    omega

/-- The original faithful action is literally the natural `A₄` action after
one point labelling. -/
def IsNaturalA4Action (G X : Type) [Group G] [MulAction G X] : Prop :=
  ∃ e : X ≃ Fin 4,
    labelledActionImage (A := G) e = alternatingGroup (Fin 4)

/-- Abstract faithful-action form of the four-point structural result. -/
theorem degreeFour_rankOne_isNaturalA4
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Nonempty X]
    (hDegree : Nat.card X = 4)
    (M : Subgroup G) [M.Normal]
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 1) :
    IsNaturalA4Action G X := by
  let e : X ≃ Fin 4 := Finite.equivFinOfCardEq hDegree
  let U := labelledActionImage (A := G) e
  let T := labelledActionNormal e M
  letI : MulAction.IsPretransitive U (Fin 4) :=
    (labelledAction_pretransitive_iff e).mp inferInstance
  have hTRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) = 1 := by
    rw [← labelledActionNormal_head e 3 M]
    exact hRank
  exact ⟨e, degreeFourPermutation_rankOne_eq_alternating U T hTRank⟩

end SymmetricSubgroupAsymptotics

end
