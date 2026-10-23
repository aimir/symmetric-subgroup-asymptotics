import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedTorusEdge
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeTorus
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The actual paired torus makes all nonzero parameters of one
q^2-element simple root group conjugate in ORIGINAL twisted E6. Burnside
therefore gives q^2 <= [G:H] for every proper subgroup H. No published
minimum-degree estimate or original automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPermutationDegree
open CFSGE6GeckPairedTorusEdge CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckRelativeTorus CFSGTwistedE6GeckOriginalPairedA2
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckDiagramCovariance CFSGSerreOrdinaryTwists
open CFSGConjugateSubgroupDegree MulAction PrimitiveSocleRawStructure

local instance (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Finite (CFSG.Models.TwistedE6 q) := original_finite q

theorem original_paired_torus_edge (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (t : (q.Extension 2)ˣ) (a : q.Extension 2) :
    generatedToOriginal q (pairedTorusGenerated q 1 t) *
      pairedOriginalHom q false 0 (Multiplicative.ofAdd a) *
    (generatedToOriginal q (pairedTorusGenerated q 1 t))⁻¹ =
      pairedOriginalHom q false 0 (Multiplicative.ofAdd (a * (t : q.Extension 2)⁻¹)) := by
  have hh : pairedTorusGenerated q 1 t * pairedInGenerated q 0 (Multiplicative.ofAdd a) *
      (pairedTorusGenerated q 1 t)⁻¹ =
        pairedInGenerated q 0 (Multiplicative.ofAdd (a * (t : q.Extension 2)⁻¹)) := by
    apply Subtype.ext
    change (pairedTorusGenerated q 1 t).val *
      rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) false 0 (Multiplicative.ofAdd a) *
      (pairedTorusGenerated q 1 t).val⁻¹ =
        rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) false 0
          (Multiplicative.ofAdd (a * (t : q.Extension 2)⁻¹))
    rw [pairedTorusGenerated_val]
    exact pairedTorus_second_on_first _ _ t a
  simpa only [map_mul, map_inv] using congrArg (generatedToOriginal q) hh

theorem extension_card_le_of_root_movement (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] {X : Type*} [Finite X]
    [MulAction (CFSG.Models.TwistedE6 q) X]
    (hmove : ∃ x : X, pairedOriginalHom q false 0 (Multiplicative.ofAdd 1) • x ≠ x) :
    Nat.card (q.Extension 2) ≤ Nat.card X := by
  letI : MulAction (Multiplicative (q.Extension 2)) X :=
    MulAction.compHom X (pairedOriginalHom q false 0)
  rw [← show Nat.card (Multiplicative (q.Extension 2)) = Nat.card (q.Extension 2) from
    Nat.card_congr Multiplicative.toAdd]
  apply card_le_of_constant_fixedBy
    (Nat.card (fixedBy X (pairedOriginalHom q false 0 (Multiplicative.ofAdd 1))))
  · intro a ha
    have ha0 : a.toAdd ≠ 0 := by
      intro he
      exact ha (congrArg Multiplicative.ofAdd he)
    let t : (q.Extension 2)ˣ := (Units.mk0 a.toAdd ha0)⁻¹
    have he := Nat.card_congr (fixedByConjugateEquiv (X := X)
      (pairedOriginalHom q false 0 (Multiplicative.ofAdd 1))
      (generatedToOriginal q (pairedTorusGenerated q 1 t)))
    rw [original_paired_torus_edge] at he
    have ht : (1 : q.Extension 2) * (t : q.Extension 2)⁻¹ = a.toAdd := by
      simp only [t, Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv, one_mul]
    rw [ht] at he
    simpa only [MulAction.fixedBy, MulAction.compHom_smul_def] using he.symm
  · obtain ⟨x, hx⟩ := hmove
    exact ⟨Multiplicative.ofAdd 1, x, hx⟩

theorem order_square_le_proper_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (H : Subgroup (CFSG.Models.TwistedE6 q)) (hH : H ≠ ⊤) : q.order^2 ≤ H.index := by
  rw [← CFSGTwistedANaturalMatrices.extension_two_card]
  change Nat.card (q.Extension 2) ≤ Nat.card (CFSG.Models.TwistedE6 q ⧸ H)
  apply extension_card_le_of_root_movement q
  apply exists_moved_coset_of_ne_one H hH
  intro he
  have hp := pairedOriginalHom_injective q false 0
    (he.trans (map_one (pairedOriginalHom q false 0)).symm)
  exact (show (1 : q.Extension 2) ≠ 0 from one_ne_zero)
    (congrArg (fun x : Multiplicative (q.Extension 2) => x.toAdd) hp)

theorem order_square_le_leastProperIndex (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedE6 q) ell) : q.order^2 ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  rw [← he]
  exact order_square_le_proper_index q H hH

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPermutationDegree
