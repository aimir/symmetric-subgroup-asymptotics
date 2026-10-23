import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeScalarTorus
import SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! A degree bound from the literal short-root action in the ORIGINAL
triality group. The actual short torus word conjugates a parameter by a
square. Weighted Burnside therefore gives q^3 <= 2[ G : H ] for every
proper subgroup H. No order formula, minimum-index theorem, or lifted
automorphism is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckPermutationDegree
open CFSGTrialityGeckOriginalSimpleParameters CFSGTrialityGeckRelativeScalarTorus
open CFSGTrialityGeckShortTorusConjugation CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckSignedSimpleParameters CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckFixedRootWords
open CFSGSerreOrdinaryTwists MulAction PrimitiveSocleRawStructure

local instance (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Finite (CFSG.Models.TrialityD4 q) :=
  Finite.of_surjective (generatedToOriginal q) (generatedToOriginal_surjective q)

def generatedShortTorus (q : CFSG.PrimePower) (c : (q.Extension 3)ˣ) :
    fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
  ⟨shortTorusWord (q.Extension 3) (definingFieldAutomorphism q 3) c,
    shortTorusWord_mem_generated q c⟩

def originalShortTorus (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (c : (q.Extension 3)ˣ) :
    CFSG.Models.TrialityD4 q := generatedToOriginal q (generatedShortTorus q c)

theorem original_short_torus_conjugation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (c : (q.Extension 3)ˣ)
    (t : q.Extension 3) :
    originalShortTorus q c * originalShortHom q false (Multiplicative.ofAdd t) *
      (originalShortTorus q c)⁻¹ =
        originalShortHom q false (Multiplicative.ofAdd (t * (c : q.Extension 3)^2)) := by
  have hh : generatedShortTorus q c * shortGeneratedHom q false (Multiplicative.ofAdd t) *
      (generatedShortTorus q c)⁻¹ =
        shortGeneratedHom q false (Multiplicative.ofAdd (t * (c : q.Extension 3)^2)) := by
    apply Subtype.ext
    exact shortTorusWord_conjugate (q.Extension 3) (definingFieldAutomorphism q 3) c t
  have he := congrArg (generatedToOriginal q) hh
  simpa only [map_mul, map_inv] using he

theorem extension_card_le_twice_of_root_movement (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] {X : Type*} [Finite X]
    [MulAction (CFSG.Models.TrialityD4 q) X]
    (hmove : ∀ a : (q.Extension 3)ˣ, ∃ x : X,
      originalShortHom q false (Multiplicative.ofAdd (a : q.Extension 3)) • x ≠ x) :
    Nat.card (q.Extension 3) ≤ 2 * Nat.card X := by
  letI : Fintype (q.Extension 3) := Fintype.ofFinite _
  letI : Fintype X := Fintype.ofFinite X
  letI : MulAction (Multiplicative (q.Extension 3)) X :=
    MulAction.compHom X (originalShortHom q false)
  apply CFSGSquareScalarPermutationDegree.card_le_twice_of_square_fixedBy
  · intro a c
    have he := Nat.card_congr
      (CFSGConjugateSubgroupDegree.fixedByConjugateEquiv (X := X)
        (originalShortHom q false (Multiplicative.ofAdd (a : q.Extension 3)))
        (originalShortTorus q c))
    rw [original_short_torus_conjugation] at he
    simpa only [MulAction.fixedBy, MulAction.compHom_smul_def] using he.symm
  · exact hmove

theorem extension_card_le_twice_proper_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (H : Subgroup (CFSG.Models.TrialityD4 q)) (hH : H ≠ ⊤) :
    Nat.card (q.Extension 3) ≤ 2 * H.index := by
  change Nat.card (q.Extension 3) ≤ 2 * Nat.card (CFSG.Models.TrialityD4 q ⧸ H)
  apply extension_card_le_twice_of_root_movement q
  intro a
  apply CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
  intro he
  apply a.ne_zero
  have hp := originalShortHom_injective q false
    (he.trans (map_one (originalShortHom q false)).symm)
  exact congrArg Multiplicative.toAdd hp

theorem order_cube_le_twice_proper_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (H : Subgroup (CFSG.Models.TrialityD4 q)) (hH : H ≠ ⊤) :
    q.order^3 ≤ 2 * H.index := by
  rw [← CFSGTrialityTripleFixedRoots.extension_three_card]
  exact extension_card_le_twice_proper_index q H hH

theorem order_cube_le_twice_leastProperIndex (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TrialityD4 q) ell) :
    q.order^3 ≤ 2 * ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  rw [← he]
  exact order_cube_le_twice_proper_index q H hH

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckPermutationDegree
