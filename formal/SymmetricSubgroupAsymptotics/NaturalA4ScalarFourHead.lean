import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The natural A4 action as one scalar-F4 head

The natural alternating group on four points is the split extension
`V4 : C3`.  This file records that fact in the exact
`ScalarFourHeadedQuotient` interface used by the index-three binary-rank
tail.  All identities are finite calculations on the displayed
permutations.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace NaturalA4ScalarFourHead

open Equiv

private def c1 : Perm (Fin 4) := swap 0 1 * swap 2 3
private def c2 : Perm (Fin 4) := swap 0 2 * swap 1 3

abbrev G := alternatingGroup (Fin 4)

private def topValue (g : Perm (Fin 4)) : ZMod 3 :=
  if g * c1 * g⁻¹ = c1 then 0
  else if g * c1 * g⁻¹ = c2 then 1
  else 2

/-- The quotient map `A4 → C3`, read from conjugation on the three
nonidentity elements of the Klein four subgroup. -/
def top : G →* CyclicThree where
  toFun g := Multiplicative.ofAdd (topValue g)
  map_one' := by decide
  map_mul' := by
    set_option maxRecDepth 10000 in decide

theorem top_surjective : Function.Surjective top := by
  set_option maxRecDepth 10000 in decide

/-- The displayed quotient has the literal Klein four subgroup as kernel. -/
@[simp] theorem top_ker : top.ker = alternatingGroup.kleinFour (Fin 4) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
    exact Abelianization.commutator_subset_ker top
  · have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup top.ker
    have hquot : Nat.card (G ⧸ top.ker) = 3 := by
      rw [Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective top top_surjective).toEquiv]
      simp [CyclicThree, Nat.card_eq_fintype_card]
    have hG : Nat.card G = 12 :=
      alternatingGroup.card_of_card_eq_four (by simp)
    have hker : Nat.card top.ker = 4 := by
      rw [hG, hquot] at hmul
      omega
    rw [hker, alternatingGroup.kleinFour_card_of_card_eq_four (by simp)]

private theorem normal_card_two_le_center
    {Q : Type*} [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal]
    (hN : Nat.card N = 2) : N ≤ Subgroup.center Q := by
  obtain ⟨u, hu, hu_unique⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro q
  by_cases hx1 : x = 1
  · simp [hx1]
  let xN : N := ⟨x, hx⟩
  let qxN : N :=
    ⟨q * x * q⁻¹, Subgroup.Normal.conj_mem (inferInstance : N.Normal) x hx q⟩
  have hxN_ne : xN ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hqxN_ne : qxN ≠ 1 := by
    intro h
    have hval : q * x * q⁻¹ = 1 := congrArg Subtype.val h
    apply hx1
    calc
      x = q⁻¹ * (q * x * q⁻¹) * q := by group
      _ = 1 := by rw [hval]; simp
  have hconj : q * x * q⁻¹ = x :=
    congrArg Subtype.val ((hu_unique qxN hqxN_ne).trans
      (hu_unique xN hxN_ne).symm)
  calc
    q * x = (q * x * q⁻¹) * q := by group
    _ = x * q := by rw [hconj]

/-- The complete normal-subgroup catalogue of the natural `A4`. -/
theorem normal_subgroup_trichotomy :
    ∀ N : Subgroup G, N.Normal →
      N = ⊥ ∨ N = alternatingGroup.kleinFour (Fin 4) ∨ N = ⊤ := by
  intro N hnormal
  letI : N.Normal := hnormal
  have hcardG : Nat.card G = 12 :=
    alternatingGroup.card_of_card_eq_four (by simp)
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hdvd : Nat.card N ∣ 12 := by
    simpa only [hcardG] using N.card_subgroup_dvd_card
  have hcases : Nat.card N = 1 ∨ Nat.card N = 2 ∨ Nat.card N = 3 ∨
      Nat.card N = 4 ∨ Nat.card N = 6 ∨ Nat.card N = 12 := by
    obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      by_contra hc0
      have : c = 0 := Nat.eq_zero_of_not_pos hc0
      subst c
      simp at hc
    have hcle : c ≤ 12 := by nlinarith
    interval_cases c <;> omega
  rcases hcases with hN | hN | hN | hN | hN | hN
  · exact Or.inl (N.eq_bot_of_card_eq hN)
  · have hcenter : N ≤ Subgroup.center G := normal_card_two_le_center N hN
    have hcenterBot : Subgroup.center G = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    have hbot : N = ⊥ := le_antisymm (by simpa only [hcenterBot] using hcenter) bot_le
    rw [hbot] at hN
    norm_num at hN
  · have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcardG, hN] at hmul
    have hqcard : Nat.card (G ⧸ N) = 4 := by omega
    have hcommQ : IsMulCommutative (G ⧸ N) :=
      ⟨⟨fun a b => IsPGroup.commutative_of_card_eq_prime_sq (p := 2)
        (by simpa using hqcard) a b⟩⟩
    have hcomm : commutator G ≤ N :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommQ
    have hKN : alternatingGroup.kleinFour (Fin 4) ≤ N := by
      rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
      exact hcomm
    have hdiv : 4 ∣ 3 := by
      have hd := Subgroup.card_dvd_of_le hKN
      rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hN] at hd
      exact hd
    norm_num at hdiv
  · have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcardG, hN] at hmul
    have hqcard : Nat.card (G ⧸ N) = 3 := by omega
    have hcommQ : IsMulCommutative (G ⧸ N) :=
      (isCyclic_of_prime_card hqcard).isMulCommutative
    have hcomm : commutator G ≤ N :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommQ
    have hKN : alternatingGroup.kleinFour (Fin 4) ≤ N := by
      rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
      exact hcomm
    exact Or.inr (Or.inl (Subgroup.eq_of_le_of_card_ge hKN (by
      rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hN])).symm)
  · have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcardG, hN] at hmul
    have hqcard : Nat.card (G ⧸ N) = 2 := by omega
    have hcommQ : IsMulCommutative (G ⧸ N) :=
      (isCyclic_of_prime_card hqcard).isMulCommutative
    have hcomm : commutator G ≤ N :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommQ
    have hKN : alternatingGroup.kleinFour (Fin 4) ≤ N := by
      rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
      exact hcomm
    have hdiv : 4 ∣ 6 := by
      have hd := Subgroup.card_dvd_of_le hKN
      rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hN] at hd
      exact hd
    norm_num at hdiv
  · exact Or.inr (Or.inr (N.eq_top_of_card_eq (hN.trans hcardG.symm)))

private def coordValue (g : Perm (Fin 4)) : ZMod 2 × ZMod 2 :=
  if g = 1 then (0, 0)
  else if g = c1 then (1, 0)
  else if g = c2 then (0, 1)
  else (1, 1)

/-- The literal Klein kernel, in additive `F4` coordinates. -/
def coord : top.ker →* ScalarFour where
  toFun g := Multiplicative.ofAdd (coordValue (g : Perm (Fin 4)))
  map_one' := by decide
  map_mul' := by decide

private theorem coord_twisted_finite : ∀ (q : G) (p : top.ker),
    coord (MulAut.conjNormal q p) =
      scalarFourTwist (Multiplicative.toAdd (top q)) (coord p) := by
  decide

theorem coord_surjective : Function.Surjective coord := by
  set_option maxRecDepth 10000 in decide

theorem coord_bijective : Function.Bijective coord := by
  set_option maxRecDepth 10000 in decide

/-- The natural `A4` quotient has one scalar-F4 layer and trivial central
kernel, hence weight one. -/
def headed : ScalarFourHeadedQuotient G where
  top := top
  top_surjective := top_surjective
  center := ⊥
  center_comm := by simp
  center_twoGroup := IsPGroup.of_bot
  layers := 0
  coord := fun _ => coord
  coord_center := by simp
  coord_joint := by
    intro p hp
    rw [Subgroup.mem_bot]
    apply coord_bijective.injective
    simpa using hp 0
  coord_twisted := by
    intro q p _
    exact coord_twisted_finite q p
  coord_zero_surjective := coord_surjective

@[simp] theorem headed_weight : headed.weight = 1 := by
  change 0 + 1 + Nat.log 2 (Nat.card (⊥ : Subgroup top.ker)) = 1
  have hcard : Nat.card (⊥ : Subgroup top.ker) = 1 := by simp
  rw [hcard]
  norm_num

end NaturalA4ScalarFourHead
end SymmetricSubgroupAsymptotics

end
