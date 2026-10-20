import SymmetricSubgroupAsymptotics.ProductProjectedEpimorphismUniform

/-! The exact ordinary RDT bounded-factor epimorphism interface, proved
with its arbitrary normal target subgroup and original projection kernel.
The proof gives constants depending only on the factor-order bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.RDTBoundedFactorEpimorphismProof
open MarkedC4 MarkedC4.RDTNormalFInterface

private theorem pi_isPGroup {I : Type} [Fintype I] (P : I → Type)
    [∀ i, Group (P i)] [∀ i, Finite (P i)]
    (hp : ∀ i, IsPGroup 2 (P i)) : IsPGroup 2 (∀ i, P i) := by
  choose n hn using fun i => (hp i).exists_card_eq
  apply IsPGroup.of_card (n := ∑ i, n i)
  rw [Nat.card_pi]
  simp_rw [hn]
  exact Finset.prod_pow_eq_pow_sum _ _ _

private theorem prod_isPGroup {A B : Type} [Group A] [Group B]
    [Finite A] [Finite B] (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) :
    IsPGroup 2 (A × B) := by
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  apply IsPGroup.of_card (n := a + b)
  rw [Nat.card_prod, ha, hb, pow_add]

/-- No source structural input is needed beyond the exact hypotheses
already present in the original retained interface. -/
theorem rdtTheorem46BinaryInput_proved : RDTTheorem46BinaryInput := by
  intro k
  refine ⟨(ProductProjectedEpimorphismUniform.uniformConstant k : ℝ), (k : ℝ),
    by exact_mod_cast ProductProjectedEpimorphismUniform.uniformConstant_pos k,
    by positivity, ?_⟩
  intro s u R _ _ P _ _ hR hP _hRcard hPcard L _hL G hπ Q _ _ _ hQ hQcard F hF dN hd
  letI : F.Normal := hF
  have hL : IsPGroup 2 L := (pi_isPGroup R hR).to_subgroup L
  have hG : IsPGroup 2 G := (prod_isPGroup hL (pi_isPGroup P hP)).to_subgroup G
  have h := ProductProjectedEpimorphismUniform.epimorphism_card_le P
    ((MonoidHom.snd L (∀ j, P j)).comp G.subtype) hG hQ hπ F k dN
    hQcard hPcard hd
  have hr : (Nat.card {f : G →* Q // Function.Surjective f} : ℝ) ≤
      (ProductProjectedEpimorphismUniform.uniformConstant k : ℝ) *
        (genRank G : ℝ) ^ k *
        (Nat.card (Subgroup.centralizer (F : Set Q)) : ℝ) ^ genRank G *
        (Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q) : ℝ) ^ dN := by
    exact_mod_cast h
  simpa only [Real.rpow_natCast] using hr

end SymmetricSubgroupAsymptotics.RDTBoundedFactorEpimorphismProof
