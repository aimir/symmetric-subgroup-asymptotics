import SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit
import SymmetricSubgroupAsymptotics.ConjugacyClassExtension
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets
import SymmetricSubgroupAsymptotics.GaronziMarotiIntransitiveNumerics

/-! The entire intransitive branch of GM induction for an actual faithful
finite action. Both factors are the original invariant-set restriction
image and its literal kernel on the complementary points. The only
induction input is GM at strictly smaller degrees at least four; no
transitive/primitive or block-action case is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.GaronziMarotiIntransitiveReduction
open PermutationCharacterRankSplit SmallPermutationClassBudgets

theorem class_cube_le_of_finite_permutation_bound
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (c : ℕ)
    (hbound : ∀ L : Subgroup (Equiv.Perm (Fin (Nat.card X))),
      Nat.card (ConjClasses L)^3 ≤ c) : Nat.card (ConjClasses G)^3 ≤ c := by
  let e : X ≃ Fin (Nat.card X) := Finite.equivFinOfCardEq rfl
  let f : G →* Equiv.Perm (Fin (Nat.card X)) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hf : Function.Injective f := by
    intro g h he
    apply (show Function.Injective (MulAction.toPermHom G X) from MulAction.toPerm_injective)
    exact e.permCongrHom.injective he
  let a : G ≃* f.range := MonoidHom.ofInjective hf
  have hc : Nat.card (ConjClasses G) ≤ Nat.card (ConjClasses f.range) :=
    Nat.card_le_card_of_surjective (ConjClasses.map a.symm.toMonoidHom)
      (ConjClasses.map_surjective a.symm.surjective)
  exact (Nat.pow_le_pow_left hc 3).trans (hbound f.range)

theorem class_card_le_small_degree
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (hpos : 1 ≤ Nat.card X) (hsmall : Nat.card X ≤ 3) :
    Nat.card (ConjClasses G) ≤ Nat.card X := by
  by_cases hone : Nat.card X ≤ 1
  · letI : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp hone
    letI : Subsingleton G := ⟨fun g h =>
      eq_of_smul_eq_smul (α := X) (fun x => Subsingleton.elim (g • x) (h • x))⟩
    have hc : Nat.card (ConjClasses G) ≤ 1 := by
      simpa only [Nat.card_unique] using Nat.card_le_card_of_surjective
        (@ConjClasses.mk G _) ConjClasses.mk_surjective
    exact hc.trans hpos
  · let f : G →* Equiv.Perm X := MulAction.toPermHom G X
    let a : G ≃* f.range := MonoidHom.ofInjective
      (show Function.Injective f from MulAction.toPerm_injective)
    have hc : Nat.card (ConjClasses G) ≤ Nat.card (ConjClasses f.range) :=
      Nat.card_le_card_of_surjective (ConjClasses.map a.symm.toMonoidHom)
        (ConjClasses.map_surjective a.symm.surjective)
    by_cases htwo : Nat.card X ≤ 2
    · have hn : Nat.card X = 2 := by omega
      exact (hc.trans (subgroup_class_card_le_two htwo f.range)).trans (by omega)
    · have hn : Nat.card X = 3 := by omega
      exact (hc.trans (subgroup_class_card_le_three hsmall f.range)).trans (by omega)

theorem invariant_set_step
    {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (S : SubMulAction G X) (hS : (S : Set X).Nonempty)
    (hC : (Sᶜ : Set X).Nonempty) (hn : 4 ≤ Nat.card X)
    (hSmaller : ∀ m : ℕ, m < Nat.card X → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L)^3 ≤ 5^(m-1)) :
    Nat.card (ConjClasses G)^3 ≤ 5^(Nat.card X-1) := by
  letI : FaithfulSMul (Kernel S) ↥(Sᶜ) := kernel_complement_faithful S
  letI : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  letI : Nonempty ↥(Sᶜ) := ⟨⟨hC.choose, hC.choose_spec⟩⟩
  have hposS : 1 ≤ Nat.card S := Nat.card_pos
  have hposC : 1 ≤ Nat.card ↥(Sᶜ) := Nat.card_pos
  have hlt := degrees_lt S hS hC
  have hsplit := conjugacyClass_card_le_normal_mul_quotient (Kernel S)
  let e := QuotientGroup.quotientKerEquivOfSurjective (projection S) (projection_surjective S)
  have hquot : Nat.card (ConjClasses (G ⧸ Kernel S)) ≤ Nat.card (ConjClasses (Image S)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  have hclass : Nat.card (ConjClasses G) ≤
      Nat.card (ConjClasses (Kernel S))*Nat.card (ConjClasses (Image S)) :=
    hsplit.trans (Nat.mul_le_mul_left _ hquot)
  have hproduct := GaronziMarotiIntransitiveNumerics.product_cube_le
    (Nat.card (ConjClasses (Kernel S))) (Nat.card (ConjClasses (Image S)))
    (Nat.card ↥(Sᶜ)) (Nat.card S) hposC hposS
    (by have he := card_split S; omega)
    (fun hc => class_card_le_small_degree (Kernel S) ↥(Sᶜ) hposC hc)
    (fun hs => class_card_le_small_degree (Image S) S hposS hs)
    (fun hc => class_cube_le_of_finite_permutation_bound (Kernel S) ↥(Sᶜ) _
      (hSmaller _ hlt.2 hc))
    (fun hs => class_cube_le_of_finite_permutation_bound (Image S) S _
      (hSmaller _ hlt.1 hs))
  have hdegree : Nat.card ↥(Sᶜ)+Nat.card S = Nat.card X := by
    have he := card_split S
    omega
  rw [hdegree] at hproduct
  exact (Nat.pow_le_pow_left hclass 3).trans hproduct

theorem intransitive_step
    {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (hnot : ¬ MulAction.IsPretransitive G X) (hn : 4 ≤ Nat.card X)
    (hSmaller : ∀ m : ℕ, m < Nat.card X → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L)^3 ≤ 5^(m-1)) :
    Nat.card (ConjClasses G)^3 ≤ 5^(Nat.card X-1) := by
  obtain ⟨S, hS, hC⟩ := exists_nonempty_proper_invariant hnot
  exact invariant_set_step S hS hC hn hSmaller

end SymmetricSubgroupAsymptotics.GaronziMarotiIntransitiveReduction
