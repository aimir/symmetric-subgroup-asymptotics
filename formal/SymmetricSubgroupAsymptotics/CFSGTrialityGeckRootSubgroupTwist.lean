import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroup

/-! The actual matrix diagram--field twist permutes ALL lattice root
subgroups. The proof transports their original Weyl-word witnesses and
uses the proved integral same-root word independence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootSubgroupTwist
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist CFSGSerreDiagram
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreQuadraticWordRootTransport CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckColumns CFSGNormTwoCartanDiagramRoots
open CFSGNormTwoCoordinateDiagramIndices CFSGNormTwoCartanDiagramWords

theorem unitTwist_raw_root (K : Type) [CommRing K] (σ : K ≃+* K)
    (neg : Bool) (i : Fin 4) (t : K) :
    unitTwist K σ (canonicalRoot rawData K neg i t) =
      canonicalRoot rawData K neg (trialityPermutation i) (σ t) := by
  rw [← transported_root_eq, unitTwist_root, transported_root_eq]

theorem unitTwist_weyl (K : Type) [CommRing K] (σ : K ≃+* K) (i : Fin 4) :
    unitTwist K σ (canonicalWeyl rawData K i) =
      canonicalWeyl rawData K (trialityPermutation i) := by
  simp only [canonicalWeyl, map_mul, unitTwist_raw_root, map_one, map_neg]

theorem unitTwist_word (K : Type) [CommRing K] (σ : K ≃+* K) (w : List (Fin 4)) :
    unitTwist K σ (canonicalWord rawData K w) =
      canonicalWord rawData K (w.map trialityPermutation) := by
  induction w with
  | nil => simp only [canonicalWord, map_one, List.map_nil]
  | cons i w ih =>
    simp only [canonicalWord, map_mul, unitTwist_weyl, ih, List.map_cons]

theorem unitTwist_root_word (K : Type) [CommRing K] (σ : K ≃+* K)
    (w : List (Fin 4)) (neg : Bool) (i : Fin 4) (t : K) :
    unitTwist K σ (rootWord rawData K w neg i t) =
      rootWord rawData K (w.map trialityPermutation) neg (trialityPermutation i) (σ t) := by
  simp only [rootWord, map_mul, map_inv, unitTwist_word, unitTwist_raw_root]

theorem word_root_subgroup_twist (K : Type) [Field K] (σ : K ≃+* K)
    (w : List (Fin 4)) (i : Fin 4) :
    (wordRootSubgroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K w i).map (unitTwist K σ).toMonoidHom =
        wordRootSubgroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
          (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
          K (w.map trialityPermutation) (trialityPermutation i) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_wordRootSubgroup_iff (CartanMatrix.D 4)
      (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      (CartanMatrix.D_off_diag_nonpos 4) K w i y).mp hy
    exact (mem_wordRootSubgroup_iff (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K (w.map trialityPermutation) (trialityPermutation i) _).mpr
        ⟨σ a, (unitTwist_root_word K σ w true i a).symm⟩
  · intro hx
    obtain ⟨a, rfl⟩ := (mem_wordRootSubgroup_iff (CartanMatrix.D 4)
      (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      (CartanMatrix.D_off_diag_nonpos 4) K (w.map trialityPermutation)
      (trialityPermutation i) x).mp hx
    refine ⟨rootWord rawData K w true i (σ.symm a), ?_, ?_⟩
    · exact (mem_wordRootSubgroup_iff (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
        K w i _).mpr ⟨σ.symm a, rfl⟩
    · change unitTwist K σ (rootWord rawData K w true i (σ.symm a)) = _
      rw [unitTwist_root_word, RingEquiv.apply_symm_apply]
      rfl

theorem root_subgroup_twist (K : Type) [Field K] (σ : K ≃+* K)
    (k : Roots (CartanMatrix.D 4)) :
    (rootSubgroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K k).map
        (unitTwist K σ).toMonoidHom =
      rootSubgroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K
        (rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k) := by
  let z := rootWitness (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) k
  have hw : wordRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index z.val.1
      (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (Index z.val.2)) = k := by
    apply Subtype.ext
    rw [← wordLinear_root, negative_val]
    exact z.property.symm
  have he := wordRoot_permutation (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    trialityPermutation triality_preserves z.val.1
    (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (Index z.val.2))
  change rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves
    (wordRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      Base Index z.val.1 (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (Index z.val.2))) =
    wordRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      Base Index (z.val.1.map trialityPermutation)
      (rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves
        (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite (Index z.val.2))) at he
  have hsimple : rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves
      (Index z.val.2 : Roots (CartanMatrix.D 4)) =
        (Index (trialityPermutation z.val.2) : Roots (CartanMatrix.D 4)) :=
    simple_rootPermutation (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      trialityPermutation triality_preserves z.val.2
  rw [hw, rootPermutation_negative, hsimple] at he
  have hd : (rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k).val =
      wordLinear (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
        Base Index (z.val.1.map trialityPermutation) (-(Index (trialityPermutation z.val.2) :
          Roots (CartanMatrix.D 4)).val) := by
    rw [congrArg Subtype.val he, ← wordLinear_root, negative_val]
  rw [rootSubgroup_eq_word (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K k z.val.1 z.val.2 z.property,
    rootSubgroup_eq_word (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K _ (z.val.1.map trialityPermutation) (trialityPermutation z.val.2) hd]
  exact word_root_subgroup_twist K σ z.val.1 z.val.2

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootSubgroupTwist
