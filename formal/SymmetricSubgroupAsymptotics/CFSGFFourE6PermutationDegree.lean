import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeTorus
import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedTorusEdge
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The first native ORIGINAL F4 root line has all its nonidentity
elements conjugate under the actual second native torus. Thus its field
cardinality is a lower bound for every proper subgroup index. This uses
the literal paired E6 edge at sigma=id, with no order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PermutationDegree
open CFSGFFourE6RelativeTorus CFSGFFourE6SimpleGeneratedParameters
open CFSGFFourE6OriginalSimpleParameters CFSGFFourE6GeneratedOriginalProjection
open CFSGE6GeckPairedTorusEdge CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckFixedOrbitRootGroups
open CFSGConjugateSubgroupDegree PrimitiveSocleRawStructure MulAction CFSG.Models.Chevalley

local instance (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Finite (Projective CartanMatrix.F₄ K) := CFSGFFourE6OriginalProjection.original_finite K

theorem original_torus_edge (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (t : Kˣ) (a : K) :
    generatedToOriginal K (torusInGenerated K 1 t) *
      originalSimpleHom K false 0 (Multiplicative.ofAdd a) *
    (generatedToOriginal K (torusInGenerated K 1 t))⁻¹ =
      originalSimpleHom K false 0 (Multiplicative.ofAdd (a * (t : K)⁻¹)) := by
  have hh : torusInGenerated K 1 t * simpleInGenerated K false 0 (Multiplicative.ofAdd a) *
      (torusInGenerated K 1 t)⁻¹ =
        simpleInGenerated K false 0 (Multiplicative.ofAdd (a * (t : K)⁻¹)) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, simpleInGenerated_val]
    change (torusInGenerated K (pairedOrbit 1) t).val *
      rawPairedHom K (RingEquiv.refl K) false 0 (Multiplicative.ofAdd a) *
      (torusInGenerated K (pairedOrbit 1) t).val⁻¹ =
        rawPairedHom K (RingEquiv.refl K) false 0 (Multiplicative.ofAdd (a * (t : K)⁻¹))
    rw [torusInGenerated_paired_val]
    exact pairedTorus_second_on_first K (RingEquiv.refl K) t a
  simpa only [map_mul, map_inv, simpleInGenerated_original] using congrArg (generatedToOriginal K) hh

theorem field_card_le_of_root_movement (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] {X : Type*} [Finite X]
    [MulAction (Projective CartanMatrix.F₄ K) X]
    (hmove : ∃ x : X, originalSimpleHom K false 0 (Multiplicative.ofAdd 1) • x ≠ x) :
    Nat.card K ≤ Nat.card X := by
  letI : MulAction (Multiplicative K) X := MulAction.compHom X (originalSimpleHom K false 0)
  rw [← show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd]
  apply card_le_of_constant_fixedBy
    (Nat.card (fixedBy X (originalSimpleHom K false 0 (Multiplicative.ofAdd 1))))
  · intro a ha
    have ha0 : a.toAdd ≠ 0 := by intro he; exact ha (congrArg Multiplicative.ofAdd he)
    let t : Kˣ := (Units.mk0 a.toAdd ha0)⁻¹
    have he := Nat.card_congr (fixedByConjugateEquiv (X := X)
      (originalSimpleHom K false 0 (Multiplicative.ofAdd 1))
      (generatedToOriginal K (torusInGenerated K 1 t)))
    rw [original_torus_edge] at he
    have ht : (1 : K) * (t : K)⁻¹ = a.toAdd := by
      simp only [t, Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv, one_mul]
    rw [ht] at he
    simpa only [MulAction.fixedBy, MulAction.compHom_smul_def] using he.symm
  · obtain ⟨x, hx⟩ := hmove
    exact ⟨Multiplicative.ofAdd 1, x, hx⟩

theorem field_card_le_proper_index (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (H : Subgroup (Projective CartanMatrix.F₄ K)) (hH : H ≠ ⊤) : Nat.card K ≤ H.index := by
  change Nat.card K ≤ Nat.card (Projective CartanMatrix.F₄ K ⧸ H)
  apply field_card_le_of_root_movement K
  apply exists_moved_coset_of_ne_one H hH
  intro he
  have hp := originalSimpleHom_injective K p false 0
    (he.trans (map_one (originalSimpleHom K false 0)).symm)
  exact (show (1 : K) ≠ 0 from one_ne_zero) (congrArg (fun z : Multiplicative K => z.toAdd) hp)

theorem field_card_le_leastProperIndex (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.F₄ K) ell) : Nat.card K ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  rw [← he]
  exact field_card_le_proper_index K p H hH

end SymmetricSubgroupAsymptotics.CFSGFFourE6PermutationDegree
