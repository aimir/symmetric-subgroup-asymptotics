import SymmetricSubgroupAsymptotics.CFSGGTwoLongTorusAction
import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalProjectiveModel
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The original pinned simple G2 model has proper-subgroup index at
least the field cardinality. The actual long-node torus conjugates all
nonzero parameters of the short root, so Burnside's orbit identity pays
the entire field size in every nontrivial coset action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPermutationDegree
open CFSGGTwoSerreMatrices CFSGGTwoRootParameters CFSGGTwoLongTorusAction
open CFSGGTwoNaturalProjectiveModel CFSGConjugateSubgroupDegree
open PrimitiveSocleRawStructure MulAction CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] (hcard : 3 ≤ Nat.card K)
  [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

def originalShortHom : Multiplicative K →* Projective CartanMatrix.G₂ K :=
  (naturalEquivOriginal K hcard).toMonoidHom.comp (rootHom K false 0)

theorem originalShortHom_injective : Function.Injective (originalShortHom K hcard) :=
  (naturalEquivOriginal K hcard).injective.comp (rootHom_injective K false 0)

theorem original_torus_edge (t : Kˣ) (a : K) :
    naturalEquivOriginal K hcard (longTorus t) *
      originalShortHom K hcard (Multiplicative.ofAdd a) *
      (naturalEquivOriginal K hcard (longTorus t))⁻¹ =
    originalShortHom K hcard (Multiplicative.ofAdd (a*(t⁻¹ : Kˣ))) := by
  simpa only [map_mul, map_inv] using
    congrArg (naturalEquivOriginal K hcard) (longTorus_short_root t a)

theorem field_card_le_of_root_movement {X : Type*} [Finite X]
    [MulAction (Projective CartanMatrix.G₂ K) X]
    (hmove : ∃ x : X, originalShortHom K hcard (Multiplicative.ofAdd 1) • x ≠ x) :
    Nat.card K ≤ Nat.card X := by
  letI : MulAction (Multiplicative K) X := MulAction.compHom X (originalShortHom K hcard)
  rw [← show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd]
  apply card_le_of_constant_fixedBy
    (Nat.card (fixedBy X (originalShortHom K hcard (Multiplicative.ofAdd 1))))
  · intro a ha
    have ha0 : a.toAdd ≠ 0 := by
      intro he
      exact ha (congrArg Multiplicative.ofAdd he)
    let t : Kˣ := (Units.mk0 a.toAdd ha0)⁻¹
    have he := Nat.card_congr (fixedByConjugateEquiv (X := X)
      (originalShortHom K hcard (Multiplicative.ofAdd 1))
      (naturalEquivOriginal K hcard (longTorus t)))
    rw [original_torus_edge] at he
    have ht : (1 : K)*(t⁻¹ : Kˣ) = a.toAdd := by
      simp only [t, inv_inv, Units.val_mk0, one_mul]
    rw [ht] at he
    simpa only [MulAction.fixedBy, MulAction.compHom_smul_def] using he.symm
  · obtain ⟨x,hx⟩ := hmove
    exact ⟨Multiplicative.ofAdd 1,x,hx⟩

include hcard in
theorem field_card_le_proper_index
    (H : Subgroup (Projective CartanMatrix.G₂ K)) (hH : H ≠ ⊤) : Nat.card K ≤ H.index := by
  letI : Finite (Projective CartanMatrix.G₂ K) :=
    Finite.of_equiv (naturalGroup K) (naturalEquivOriginal K hcard).toEquiv
  change Nat.card K ≤ Nat.card (Projective CartanMatrix.G₂ K ⧸ H)
  apply field_card_le_of_root_movement K hcard
  apply exists_moved_coset_of_ne_one H hH
  intro he
  have hp := originalShortHom_injective K hcard
    (he.trans (map_one (originalShortHom K hcard)).symm)
  exact (show (1 : K) ≠ 0 from one_ne_zero)
    (congrArg (fun z : Multiplicative K => z.toAdd) hp)

include hcard in
theorem field_card_le_leastProperIndex (ell : ℕ)
    (hell : LeastProperIndex (Projective CartanMatrix.G₂ K) ell) : Nat.card K ≤ ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [← he]
  exact field_card_le_proper_index K hcard H hH

end SymmetricSubgroupAsymptotics.CFSGGTwoPermutationDegree
