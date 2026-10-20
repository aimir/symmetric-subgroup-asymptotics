import SymmetricSubgroupAsymptotics.PreE7FiniteMixedSmallGroupMenu
import SymmetricSubgroupAsymptotics.McIverNeumannPermutationSection
import SymmetricSubgroupAsymptotics.TransitiveBinaryGenerators
import SymmetricSubgroupAsymptotics.GeneratedLiteralImage

/-!
One complete coefficient estimate for every literal degree-sixteen action.
McIver--Neumann gives eight ordinary generators for each subgroup. Encoding
normal states and quotient automorphisms therefore costs at most 2^1024,
inside the fixed menu allowance. No action order, normal census, or row
coefficient is supplied as a premise. The quotient-socle bound remains a
separate structural obligation.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace PreE7FiniteMixedPermutationMenu

variable (hMN : McIverNeumannPermutationGeneratorBound)

include hMN in
theorem literal_generating_tuple (J : Subgroup (Equiv.Perm (Fin 16))) :
    ∃ x : Fin 8 → J, Subgroup.closure (Set.range x) = ⊤ := by
  obtain ⟨S, hS, hsize⟩ := hMN 16 J (by omega)
  let e : {x // x ∈ S} ≃ Fin S.card := S.equivFin
  let x : Fin S.card → J := fun j => (e.symm j).1
  have hrange : Set.range x = (S : Set J) := by
    ext g
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, congrArg Subtype.val (e.symm_apply_apply ⟨g, hg⟩)⟩
  apply exists_generating_tuple_of_length_le x _ (by omega : S.card ≤ 8)
  rwa [hrange]

include hMN in
theorem generating_tuple_of_embedding {G : Type} [Group G]
    (f : G →* Equiv.Perm (Fin 16)) (hf : Function.Injective f) :
    ∃ x : Fin 8 → G, Subgroup.closure (Set.range x) = ⊤ := by
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hf, f.rangeRestrict_surjective⟩
  obtain ⟨x, hx⟩ := literal_generating_tuple hMN f.range
  refine ⟨fun j => e.symm (x j), ?_⟩
  have h := e.symm.toMonoidHom.map_closure (Set.range x)
  rw [hx, Subgroup.map_top_of_surjective _ e.symm.surjective] at h
  have hi : e.symm '' Set.range x = Set.range (fun j => e.symm (x j)) := by
    ext g
    constructor
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨x j, ⟨j, rfl⟩, rfl⟩
  change ⊤ = Subgroup.closure (e.symm '' Set.range x) at h
  rw [hi] at h
  exact h.symm

include hMN in
theorem subgroup_tuple (J : Subgroup (Equiv.Perm (Fin 16))) (H : Subgroup J) :
    ∃ x : Fin 8 → J, Subgroup.closure (Set.range x) = H := by
  let f := J.subtype.comp H.subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  obtain ⟨x, hx⟩ := generating_tuple_of_embedding hMN f hf
  refine ⟨fun j => (x j : J), ?_⟩
  have h := GeneratedLiteralImage.range_eq H.subtype x (fun j => (x j : J))
    (Equiv.refl _) hx (fun _ => rfl)
  simpa using h.symm

theorem literal_card_le (J : Subgroup (Equiv.Perm (Fin 16))) :
    Nat.card J ≤ 2 ^ 64 := by
  calc
    Nat.card J ≤ Nat.card (Equiv.Perm (Fin 16)) := Subgroup.card_le_card_group J
    _ = Nat.factorial 16 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    _ ≤ 16 ^ 16 := Nat.factorial_le_pow 16
    _ = 2 ^ 64 := by norm_num

include hMN in
theorem state_card_le (J : Subgroup (Equiv.Perm (Fin 16)))
    (R : FiniteNormalStateRegistry J) : Nat.card R.State ≤ 2 ^ 512 := by
  choose x hx using subgroup_tuple hMN J
  have hi : Function.Injective (fun j : R.State => x (R.state j)) := by
    intro j k h
    apply R.state_injective
    change x (R.state j) = x (R.state k) at h
    rw [← hx (R.state j), ← hx (R.state k)]
    exact congrArg (fun y : Fin 8 → J => Subgroup.closure (Set.range y)) h
  calc
    Nat.card R.State ≤ Nat.card (Fin 8 → J) := Nat.card_le_card_of_injective _ hi
    _ = Nat.card J ^ 8 := by rw [Nat.card_fun, Nat.card_fin]
    _ ≤ (2 ^ 64) ^ 8 := Nat.pow_le_pow_left (literal_card_le J) 8
    _ = 2 ^ 512 := by rw [← pow_mul]

include hMN in
/-- Encode an automorphism on the quotient by its images of generators
of the original group. The literal quotient denominator is unchanged. -/
theorem quotient_aut_card_le (J : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup J) [N.Normal] : Nat.card ((J ⧸ N) ≃* (J ⧸ N)) ≤ 2 ^ 512 := by
  obtain ⟨S, hS, hsize⟩ := hMN 16 J (by omega)
  let q := QuotientGroup.mk' N
  let encode : ((J ⧸ N) ≃* (J ⧸ N)) → (J →* J ⧸ N) :=
    fun e => e.toMonoidHom.comp q
  have hi : Function.Injective encode := by
    intro e f h
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact DFunLike.congr_fun h x
  have hcard : Nat.card (J ⧸ N) ≤ 2 ^ 64 :=
    (Nat.card_le_card_of_surjective q (QuotientGroup.mk'_surjective N)).trans
      (literal_card_le J)
  calc
    Nat.card ((J ⧸ N) ≃* (J ⧸ N)) ≤ Nat.card (J →* J ⧸ N) :=
      Nat.card_le_card_of_injective _ hi
    _ ≤ Nat.card (J ⧸ N) ^ S.card := monoidHom_card_le_pow_of_closure S hS
    _ ≤ Nat.card (J ⧸ N) ^ 8 := Nat.pow_le_pow_right Nat.card_pos (by omega)
    _ ≤ (2 ^ 64) ^ 8 := Nat.pow_le_pow_left hcard 8
    _ = 2 ^ 512 := by rw [← pow_mul]

include hMN in
theorem state_sum_le (J : Subgroup (Equiv.Perm (Fin 16)))
    (R : FiniteNormalStateRegistry J) (f : R.State → ℝ)
    (hf : ∀ j, f j ≤ (2 : ℝ) ^ (512 : ℕ)) :
    (∑ j, f j) ≤ (2 : ℝ) ^ (1024 : ℕ) := by
  calc
    (∑ j, f j) ≤ ∑ _j : R.State, (2 : ℝ) ^ (512 : ℕ) :=
      Finset.sum_le_sum (fun j _ => hf j)
    _ = (Nat.card R.State : ℝ) * (2 : ℝ) ^ (512 : ℕ) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ (2 : ℝ) ^ (512 : ℕ) * (2 : ℝ) ^ (512 : ℕ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast state_card_le hMN J R
    _ = (2 : ℝ) ^ (1024 : ℕ) := by rw [← pow_add]

theorem allowance (b : ℕ) : (2 : ℝ) ^ (1024 : ℕ) ≤
    (2 : ℝ) ^ (16 * (16 : ℝ) * Real.log ((16 + b + 2 : ℕ) : ℝ) ^ 2) := by
  have harg : (9 : ℝ) < ((16 + b + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 9 < 16 + b + 2 by omega)
  have hexp : Real.exp (2 : ℝ) < 9 := by
    have hm := mul_lt_mul Real.exp_one_lt_three Real.exp_one_lt_three.le
      (Real.exp_pos (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 3)
    have he : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      calc
        Real.exp (2 : ℝ) = Real.exp ((1 : ℝ) + 1) := congrArg Real.exp (by norm_num)
        _ = Real.exp 1 * Real.exp 1 := Real.exp_add (1 : ℝ) 1
    rw [he]
    norm_num at hm
    exact hm
  have hlog : (2 : ℝ) ≤ Real.log ((16 + b + 2 : ℕ) : ℝ) :=
    ((Real.lt_log_iff_exp_lt (by positivity)).2 (hexp.trans harg)).le
  calc
    (2 : ℝ) ^ (1024 : ℕ) = (2 : ℝ) ^ (1024 : ℝ) :=
      (Real.rpow_natCast (2 : ℝ) 1024).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      nlinarith [sq_nonneg (Real.log ((16 + b + 2 : ℕ) : ℝ) - 2)])

variable (i : PreE7NonPairActionClass 16)
  (R : FiniteNormalStateRegistry (preE7NonPairAction 16 i))
  {t : ℕ} (ht : t ≤ 2)
  (hgen : ∀ N : {N : Subgroup (preE7NonPairAction 16 i) // N.Normal},
    SocleNormalGeneratorBound (preE7NonPairAction 16 i ⧸ N.1) t)
  (hZmud : ZmudFaithfulCharacterTupleInput)

noncomputable def menu : PreE7FiniteMixedCharacterMenuData 16 i where
  axes := PreE7FiniteMixedSmallGroupMenu.axes i R ht hgen hZmud
  main_state_total_bound b := by
    apply (state_sum_le hMN _ R _ ?_).trans (allowance b)
    intro j
    change (if (⊤ : Subgroup (preE7NonPairAction 16 i)) ≤ (R.normalAxis j).1
      then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (512 : ℕ)
    split_ifs
    · exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    · positivity
  tail_state_total_bound b := by
    apply (state_sum_le hMN _ R _ ?_).trans (allowance b)
    intro j
    change (if (⊤ : Subgroup (preE7NonPairAction 16 i)) ≤ (R.normalAxis j).1
      then (0 : ℝ) else
        (Nat.card ((preE7NonPairAction 16 i ⧸ (R.normalAxis j).1) ≃*
          (preE7NonPairAction 16 i ⧸ (R.normalAxis j).1)) : ℝ)) ≤ (2 : ℝ) ^ (512 : ℕ)
    split_ifs
    · positivity
    · exact_mod_cast quotient_aut_card_le hMN _ (R.normalAxis j).1

/-- A proved structural quotient-socle family is sufficient for the
complete mixed row; no order certificate or normal-state census remains. -/
noncomputable def importedRow : DegreeTwoDegreeSixteenImportedRow i :=
  .mixed (menu hMN i R ht hgen hZmud)

noncomputable def censusFreeImportedRow
    (i : PreE7NonPairActionClass 16) {t : ℕ} (ht : t ≤ 2)
    (hgen : ∀ N : {N : Subgroup (preE7NonPairAction 16 i) // N.Normal},
      SocleNormalGeneratorBound (preE7NonPairAction 16 i ⧸ N.1) t)
    (hZmud : ZmudFaithfulCharacterTupleInput) : DegreeTwoDegreeSixteenImportedRow i :=
  importedRow hMN i FiniteNormalStateRegistry.allNormals ht hgen hZmud

end PreE7FiniteMixedPermutationMenu
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
