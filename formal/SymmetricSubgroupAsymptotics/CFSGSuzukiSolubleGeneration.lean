import SymmetricSubgroupAsymptotics.CFSGSuzukiNormalizerStep
import SymmetricSubgroupAsymptotics.CFSGSemisimpleSocleChart
import SymmetricSubgroupAsymptotics.MarkedC4AschbacherGuralnickSolubleGeneration

/-! Suzuki's induction reduces soluble generation of every finite group
to the actual good-Sylow witnesses in its nonabelian simple factors.
The theorem is a conditional generic reduction; it does not assert the
remaining concrete CFSG model witnesses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReduction

private theorem suzuki_proper_card_lt {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (hK : K ≠ ⊤) : Nat.card K < Nat.card G := by
  conv_rhs => rw [← K.card_mul_index]
  exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr (Subgroup.one_lt_index_of_ne_top hK)

private theorem suzuki_quotient_card_lt {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (hN : N ≠ ⊥) : Nat.card (G ⧸ N) < Nat.card G := by
  conv_rhs => rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr (N.one_lt_card_iff_ne_bot.mpr hN)

theorem soluble_suzuki_witness (G : Type) [Group G] [Finite G] [IsSolvable G] :
    ∃ (S : Subgroup G) (g : G), IsSolvable S ∧ Intravariant S ∧
      Subgroup.normalizer (S : Set G) = S ∧ solubleRadical G ≤ S ∧
        Subgroup.closure ((S : Set G) ∪ S.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  refine ⟨⊤, 1, inferInstance, ?_, Subgroup.normalizer_eq_top ⊤, le_top, ?_⟩
  · intro a
    refine ⟨1, ?_⟩
    exact (Subgroup.map_top_of_surjective a.toMonoidHom a.surjective).trans
      (Subgroup.map_top_of_surjective (MulAut.conj (1 : G)).toMonoidHom
        (MulAut.conj (1 : G)).surjective).symm
  · apply top_unique
    intro g _
    exact Subgroup.subset_closure (Or.inl (Subgroup.mem_top g))

/-- The stronger Suzuki witness is established by genuine strict order
induction. Every witness contains the actual soluble radical. -/
theorem suzuki_witness_of_simple_goodSylow
    (leaf : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T],
      ¬ IsMulCommutative T → ∃ p, GoodSylowPrime T p)
    (G : Type) [Group G] [Finite G] :
    ∃ (S : Subgroup G) (g : G), IsSolvable S ∧ Intravariant S ∧
      Subgroup.normalizer (S : Set G) = S ∧ solubleRadical G ≤ S ∧
        Subgroup.closure ((S : Set G) ∪ S.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  suffices aux : ∀ n : ℕ, ∀ (A : Type) [Group A] [Finite A], Nat.card A = n →
      ∃ (S : Subgroup A) (g : A), IsSolvable S ∧ Intravariant S ∧
        Subgroup.normalizer (S : Set A) = S ∧ solubleRadical A ≤ S ∧
          Subgroup.closure ((S : Set A) ∪ S.map (MulAut.conj g).toMonoidHom) = ⊤ by
    exact aux (Nat.card G) G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ hcard
    rcases subsingleton_or_nontrivial A with hsub | hnon
    · letI suzukiInduction_subsingleton : Subsingleton A := hsub
      exact soluble_suzuki_witness A
    · letI suzukiInduction_nontrivial : Nontrivial A := hnon
      by_cases hR : solubleRadical A = ⊥
      · let E := finiteGroupSocle A
        obtain ⟨C⟩ := radicalFreeSocle_semisimple A hR
        have hgood (i : C.ι) : ∃ p, GoodSylowPrime (C.factor i) p := by
          letI suzukiInduction_simpleFactor : IsSimpleGroup (C.factor i) := C.simple i
          apply leaf (C.factor i)
          intro hcomm
          obtain ⟨t, ht⟩ := exists_ne (1 : C.factor i)
          apply ht
          exact C.centerless i t (fun u => isMulCommutative_iff.mp hcomm t u)
        obtain ⟨H, x, hHsol, hHinv, hHself, hEgen⟩ :=
          semisimple_soluble_generation_of_equiv C.factor C.simple C.centerless hgood C.equiv.symm
        let N := Subgroup.normalizer (H.map E.subtype : Set A)
        have hN : N ≠ ⊤ := chosen_normalizer_proper_of_radical_free hR E
          (finiteGroupSocle_ne_bot A) H hHsol hHself
        have hNcard : Nat.card N < n := by
          rw [← hcard]
          exact suzuki_proper_card_lt hN
        obtain ⟨S, y, hSsol, hSinv, hSself, hSrad, hNgen⟩ := ih (Nat.card N) hNcard N rfl
        exact suzuki_normalizer_step hR E H x hHsol hHinv hHself hEgen
          S y hSsol hSinv hSself hSrad hNgen
      · have hQcard : Nat.card (A ⧸ solubleRadical A) < n := by
          rw [← hcard]
          exact suzuki_quotient_card_lt hR
        obtain ⟨S, z, hSsol, hSinv, hSself, _, hSgen⟩ :=
          ih (Nat.card (A ⧸ solubleRadical A)) hQcard (A ⧸ solubleRadical A) rfl
        exact suzuki_quotient_step (solubleRadical A) S z hSsol hSinv hSself hSgen

/-- The only remaining leaf is the actual simple-group Sylow-normalizer
generation statement. All extension, semisimple and radical steps above
are proved, and the published output keeps its original ordinary semantics. -/
theorem aschbacherGuralnick_of_simple_goodSylow
    (leaf : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T],
      ¬ IsMulCommutative T → ∃ p, GoodSylowPrime T p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  intro G _ _
  obtain ⟨S, g, hsol, _, _, _, hgen⟩ := suzuki_witness_of_simple_goodSylow leaf G
  exact ⟨S, g, hsol, one_extra_generator_of_two_conjugates S g hgen⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
