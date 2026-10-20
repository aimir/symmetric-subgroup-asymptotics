import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterCoordinates
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterKernel

/-! Sparse scalar coordinates from ambient kernel generators. Quotient-
sized Schreier generators already generate the actual kernel in the whole
original group, so no separate intrinsic kernel enumeration is required.
Actual radical word reductions determine all their character values. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

variable (p : ℕ) [Fact p.Prime] {G ι : Type} [Group G]

theorem relativeHead_le_ambient_wordCoordinates
    (N : Subgroup G) [N.Normal] (g : ι → N)
    (hgen : Subgroup.closure (Set.range (fun i => (g i : G)))=N)
    {r : ℕ} (selected : Fin r → N) (words : ι → List (Fin r))
    (hwords : ∀ i, ((g i * (((words i).map selected).prod)⁻¹ : N) : G) ∈
      primeRelativeRadical p N) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ r := by
  let ev : primeRelativeCharacters p N →ₗ[ZMod p] (Fin r → ZMod p) := {
    toFun chi j := chi.1 (Additive.ofMul (selected j))
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hi : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro chi hchi
    have hz (j : Fin r) : chi.1 (Additive.ofMul (selected j))=0 := congrFun hchi j
    have hzero (i : ι) : chi.1 (Additive.ofMul (g i))=0 := by
      rw [primeRelativeCharacter_eq_of_mul_inv_mem_radical p N chi _ _ (hwords i),
        primeRelativeCharacter_word]
      have he : (fun j : Fin r => chi.1 (Additive.ofMul (selected j)))=(fun _ => 0) :=
        funext hz
      rw [he]
      simp
    have hN : N ≤ primeRelativeCharacterKernel p N chi := by
      apply hgen.ge.trans
      apply (Subgroup.closure_le (primeRelativeCharacterKernel p N chi)).mpr
      rintro _ ⟨i,rfl⟩
      exact (coe_mem_primeRelativeCharacterKernel_iff p N chi (g i)).mpr (hzero i)
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro n
    exact (coe_mem_primeRelativeCharacterKernel_iff p N chi n.toMul).mp
      (hN n.toMul.property)
  have h := ev.finrank_le_finrank_of_injective hi
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] using h

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
