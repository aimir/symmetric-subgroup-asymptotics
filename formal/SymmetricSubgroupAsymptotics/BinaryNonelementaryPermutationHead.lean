import SymmetricSubgroupAsymptotics.BinarySquareActionStructure
import SymmetricSubgroupAsymptotics.SemiregularFourPermutationHead
import SymmetricSubgroupAsymptotics.PermutationOrbitHeadSection
import SymmetricSubgroupAsymptotics.BinaryHalfPointBlocks

/-! The natural-module quarter bound for every nonelementary original
transitive binary action. The smaller actions are the actual orbits of an
actual index-two subgroup. The elementary terminal is detected by a literal
square in the original action, not by a finite catalogue or capacity input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics

open BinarySquareActionStructure

/-- Every natural submodule of a finite transitive binary action whose
permutation image is not elementary has head at most degree/4. The action
may have a kernel; nonelementarity is tested in that same original action. -/
theorem twoGroup_permutationSubrepresentationHead_le_quarter_of_not_elementary
    {k G X : Type} [Field k] [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G)
    (hnon : ¬SquaresActTrivially (G := G) (X := X))
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k
      (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤ Nat.card X / 4 := by
  classical
  suffices hh : ∀ n (G X : Type) [Group G] [Finite G] [Finite X]
      [MulAction G X] [MulAction.IsPretransitive G X], IsPGroup 2 G → Nat.card X = n →
      ¬SquaresActTrivially (G := G) (X := X) →
      ∀ M : Subrepresentation (permutationFunctionRepresentation k G X),
      Module.finrank k
        (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤ Nat.card X / 4 from
    hh _ G X hG rfl hnon M
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G X _ _ _ _ _ hG hn hnon M
    letI := Fintype.ofFinite X
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := not_forall.mp hnon
    obtain ⟨x₀, hx₀⟩ := not_forall.mp hg
    letI : Nontrivial X := ⟨⟨g ^ 2 • x₀, x₀, hx₀⟩⟩
    have hX : 1 < Nat.card X := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hG
      (MulAction.stabilizer G x₀) ⊤ le_top
    have hdegree : Nat.card X = 2 ^ s.length := by
      simpa only [Subgroup.relIndex_top_right,
        MulAction.index_stabilizer_of_transitive G x₀] using s.relIndex
    have hs : 0 < s.length := by
      by_contra he
      have hz : s.length = 0 := by omega
      rw [hz, pow_zero] at hdegree
      omega
    let r := s.length - 1
    have hr : r + 1 = s.length := by dsimp [r]; omega
    let K := s.subgroup r
    have hi : K.index = 2 := by
      have he := s.step_index r (by dsimp [r]; omega)
      rw [hr, s.last, Subgroup.relIndex_top_right] at he
      exact he
    letI : K.Normal := K.normal_of_index_eq_two hi
    by_cases hel : SquaresActTrivially (G := K) (X := X)
    · obtain ⟨hfour, hsquare⟩ := semiregular_four_of_index_two_elementary_kernel
        K hi hel g x₀ hx₀
      exact permutationSubrepresentationHead_le_quarter_of_semiregular_four
        g hfour hsquare M
    · have hmove : ∃ (a : K) (x : X), a ^ 2 • x ≠ x := by
        obtain ⟨a, ha⟩ := not_forall.mp hel
        obtain ⟨x, hx⟩ := not_forall.mp ha
        exact ⟨a, x, hx⟩
      have hcontains : MulAction.stabilizer G x₀ ≤ K :=
        s.le_at r (by dsimp [r]; omega)
      have horbits : Nat.card (MulAction.orbitRel.Quotient K X) = 2 := by
        rw [normal_orbit_classes_card_eq_index K x₀, sup_of_le_left hcontains]
        exact hi
      have hsmall (o : MulAction.orbitRel.Quotient K X) : Nat.card o.orbit < Nat.card X := by
        have hm := normal_orbit_card_mul_classes K x₀
        rw [horbits] at hm
        have he := normal_orbit_card_eq K x₀ o
        letI : Nonempty o.orbit := ⟨⟨o.nonempty_orbit.choose, o.nonempty_orbit.choose_spec⟩⟩
        have hp : 0 < Nat.card o.orbit := Nat.card_pos
        omega
      let MK : Subrepresentation (permutationFunctionRepresentation k K X) := {
        toSubmodule := M.toSubmodule
        apply_mem_toSubmodule := fun a _ hm => M.apply_mem_toSubmodule (a : G) hm }
      let q : MK.toSubmodule →ₗ[k] M.toRepresentation.Coinvariants :=
        Representation.Coinvariants.mk M.toRepresentation
      have hq : Function.Surjective q := Representation.Coinvariants.mk_surjective _
      have htrivial (a : K) (m : MK.toSubmodule) :
          q (MK.toRepresentation a m) = q m :=
        Representation.Coinvariants.mk_self_apply M.toRepresentation (a : G) m
      have hcap (o : MulAction.orbitRel.Quotient K X)
          (S : Subrepresentation (permutationFunctionRepresentation k K o.orbit)) :
          Module.finrank k
            (S.toRepresentation.IntertwiningMap (Representation.trivial k K k)) ≤
              Nat.card o.orbit / 4 := by
        apply ih (Nat.card o.orbit) (by have := hsmall o; omega) K o.orbit
          (hG.to_subgroup K) rfl _ S
        intro he
        obtain ⟨a, x, hx⟩ := normal_orbit_exists_square_move K hmove o
        exact hx (he a x)
      have hb := permutation_trivial_quotient_weighted_finrank_le
        1 4 (fun o : MulAction.orbitRel.Quotient K X => Nat.card o.orbit / 4)
        hcap (fun o => by
          change 4 * (Nat.card o.orbit / 4) ≤ 1 * Nat.card o.orbit
          simpa only [one_mul, mul_comm] using Nat.div_mul_le_self (Nat.card o.orbit) 4)
        MK q hq htrivial
      rw [← representationHead_finrank_eq_coinvariants] at hb
      omega

/-- For a faithful original action, elementary means literally every
original element squares to one. No action-image predicate is left implicit. -/
theorem twoGroup_faithful_permutationSubrepresentationHead_le_quarter
    {k G X : Type} [Field k] [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hnon : ¬∀ g : G, g ^ 2 = 1)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k
      (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤ Nat.card X / 4 := by
  apply twoGroup_permutationSubrepresentationHead_le_quarter_of_not_elementary hG _ M
  intro h
  exact hnon (squaresActTrivially_iff_pow_two.mp h)

/-- In defining characteristic, the same generic quarter theorem gives
actual module generators uniformly over all original natural submodules. -/
theorem twoGroup_permutationSubrepresentationGeneratedBy_quarter_of_not_elementary
    {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hnon : ¬SquaresActTrivially (G := G) (X := X)) :
    ∀ M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X),
      RepresentationGeneratedBy M.toRepresentation (Nat.card X / 4) := by
  letI := Fintype.ofFinite X
  exact pGroup_uniformSubrepresentationGeneratorBound_of_head_le hG
    (permutationFunctionRepresentation (ZMod 2) G X) (Nat.card X / 4)
    (twoGroup_permutationSubrepresentationHead_le_quarter_of_not_elementary hG hnon)

end SymmetricSubgroupAsymptotics
