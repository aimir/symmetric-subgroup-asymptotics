import SymmetricSubgroupAsymptotics.PermutationOrbitCoverGenerators
import Mathlib.GroupTheory.GroupAction.Quotient

/-! A faithful order-seven action on eight actual points has at most two
orbits. This is an orbit-stabilizer argument, not a permutation census. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics

/-- Faithfulness rules out eight fixed points; the remaining prime orbit
has seven points, leaving at most one further orbit. -/
theorem primeSeven_eight_orbit_count
    {C X : Type} [Group C] [Finite C] [MulAction C X]
    [FaithfulSMul C X] [Finite X]
    (hC : Nat.card C = 7) (hX : Nat.card X = 8) :
    Nat.card (MulAction.orbitRel.Quotient C X) ≤ 2 := by
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite X
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient C X)
  have horbit (x : X) : Nat.card (MulAction.orbit C x) = 1 ∨
      Nat.card (MulAction.orbit C x) = 7 := by
    letI := Fintype.ofFinite (MulAction.orbit C x)
    letI := Fintype.ofFinite (MulAction.stabilizer C x)
    have hm := MulAction.card_orbit_mul_card_stabilizer_eq_card_group C x
    have hd : Fintype.card (MulAction.orbit C x) ∣ 7 := by
      refine ⟨Fintype.card (MulAction.stabilizer C x), ?_⟩
      simpa only [Nat.card_eq_fintype_card] using
        (show Fintype.card C = 7 by simpa only [Nat.card_eq_fintype_card] using hC).symm.trans hm.symm
    simpa only [Nat.card_eq_fintype_card] using (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd
  have hlarge : ∃ q : MulAction.orbitRel.Quotient C X,
      Nat.card (MulAction.orbit C q.out) = 7 := by
    by_contra hh
    push Not at hh
    have hone (q : MulAction.orbitRel.Quotient C X) :
        Nat.card (MulAction.orbit C q.out) = 1 := (horbit q.out).resolve_right (hh q)
    have hfixed (g : C) (x : X) : g • x = x := by
      let q : MulAction.orbitRel.Quotient C X := Quotient.mk'' x
      have hx : x ∈ MulAction.orbit C q.out := by
        have heq : (Quotient.mk'' q.out : MulAction.orbitRel.Quotient C X) =
            Quotient.mk'' x := Quotient.out_eq' q
        exact (Quotient.exact heq.symm : x ∈ MulAction.orbit C q.out)
      obtain ⟨a, ha⟩ := hx
      have hf := (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).mpr
        (show Fintype.card (MulAction.orbit C q.out) = 1 by
          simpa only [Nat.card_eq_fintype_card] using hone q)
      change a • q.out = x at ha
      change ∀ c : C, c • q.out = q.out at hf
      rw [← ha, hf a, hf g]
    have hsub : Subsingleton C := ⟨fun a b => eq_of_smul_eq_smul (fun x =>
      (hfixed a x).trans (hfixed b x).symm)⟩
    have hc := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  obtain ⟨q, hq⟩ := hlarge
  have hsum : (∑ o : MulAction.orbitRel.Quotient C X,
      Nat.card (MulAction.orbit C o.out)) = 8 := by
    rw [← Nat.card_sigma]
    exact (Nat.card_congr (MulAction.selfEquivSigmaOrbits C X).symm).trans hX
  have hrest : (Finset.univ.erase q).card ≤
      ∑ o ∈ Finset.univ.erase q, Nat.card (MulAction.orbit C o.out) := by
    calc
      _ = ∑ _o ∈ Finset.univ.erase q, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun o _ => by
        rcases horbit o.out with h | h <;> omega
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun o : MulAction.orbitRel.Quotient C X => Nat.card (MulAction.orbit C o.out))
    (Finset.mem_univ q)
  dsimp only at hsplit
  rw [hq, hsum] at hsplit
  have he := Finset.card_erase_of_mem (Finset.mem_univ q)
  simp only [Finset.card_univ] at he
  simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
    (show Fintype.card (MulAction.orbitRel.Quotient C X) ≤ 2 by omega)

end SymmetricSubgroupAsymptotics
