import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramFieldTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIntegral
import SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroup

/-! Actual diagram--field twists permute every literal integral lattice
root subgroup. The proof transports original word witnesses and invokes
the checked integral same-root word independence; no finite-root census
or source-faithfulness premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramFieldRootTwist
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckIntegralRealization
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreQuadraticWordRootTransport CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckColumns CFSGNormTwoCartanDiagramRoots
open CFSGNormTwoCoordinateDiagramIndices CFSGNormTwoCartanDiagramWords
open CFSGNormTwoCoordinateDiagramIntegral
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (p : Equiv.Perm (Fin r)) (hA : ∀i j,A (p i) (p j)=A i j)
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

abbrev unitTwist (K : Type) [CommRing K] (sigma : K≃+*K) :=
  CFSGSerreQuadraticDiagramFieldTwist.unitTwist (combinedIndex A hd hs hp ho p hA) K sigma

include hd hs hp ho p hA

omit [(rootPairing A hs hp).IsReduced] in
theorem unitTwist_raw_root (K : Type) [CommRing K] (sigma : K≃+*K)
    (neg : Bool) (i : Fin r) (t : K) :
    unitTwist A hd hs hp ho p hA K sigma (canonicalRoot D K neg i t)=
      canonicalRoot D K neg (p i) (sigma t) :=
  CFSGSerreQuadraticDiagramFieldTwist.unitTwist_root D p (combinedIndex A hd hs hp ho p hA)
    (integerRoot_covariance A hd hs hp ho p hA) K sigma neg i t

omit [(rootPairing A hs hp).IsReduced] in
theorem unitTwist_weyl (K : Type) [CommRing K] (σ : K ≃+* K) (i : Fin r) :
    unitTwist A hd hs hp ho p hA K σ (canonicalWeyl D K i) =
      canonicalWeyl D K (p i) := by
  simp only [canonicalWeyl, map_mul, unitTwist_raw_root, map_one, map_neg]

omit [(rootPairing A hs hp).IsReduced] in
theorem unitTwist_word (K : Type) [CommRing K] (σ : K ≃+* K) (w : List (Fin r)) :
    unitTwist A hd hs hp ho p hA K σ (canonicalWord D K w) =
      canonicalWord D K (w.map p) := by
  induction w with
  | nil => simp only [canonicalWord, map_one, List.map_nil]
  | cons i w ih =>
    simp only [canonicalWord, map_mul, unitTwist_weyl, ih, List.map_cons]

omit [(rootPairing A hs hp).IsReduced] in
theorem unitTwist_root_word (K : Type) [CommRing K] (σ : K ≃+* K)
    (w : List (Fin r)) (neg : Bool) (i : Fin r) (t : K) :
    unitTwist A hd hs hp ho p hA K σ (rootWord D K w neg i t) =
      rootWord D K (w.map p) neg (p i) (σ t) := by
  simp only [rootWord, map_mul, map_inv, unitTwist_word, unitTwist_raw_root]

theorem word_root_subgroup_twist (K : Type) [Field K] (σ : K ≃+* K)
    (w : List (Fin r)) (i : Fin r) :
    (wordRootSubgroup A hd
      hs hp ho
      K w i).map (unitTwist A hd hs hp ho p hA K σ).toMonoidHom =
        wordRootSubgroup A hd
          hs hp ho
          K (w.map p) (p i) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_wordRootSubgroup_iff A
      hd hs hp
      ho K w i y).mp hy
    exact (mem_wordRootSubgroup_iff A hd
      hs hp ho
      K (w.map p) (p i) _).mpr
        ⟨σ a, (unitTwist_root_word A hd hs hp ho p hA K σ w true i a).symm⟩
  · intro hx
    obtain ⟨a, rfl⟩ := (mem_wordRootSubgroup_iff A
      hd hs hp
      ho K (w.map p)
      (p i) x).mp hx
    refine ⟨rootWord D K w true i (σ.symm a), ?_, ?_⟩
    · exact (mem_wordRootSubgroup_iff A hd
        hs hp ho
        K w i _).mpr ⟨σ.symm a, rfl⟩
    · change unitTwist A hd hs hp ho p hA K σ (rootWord D K w true i (σ.symm a)) = _
      rw [unitTwist_root_word, RingEquiv.apply_symm_apply]

theorem root_subgroup_twist (K : Type) [Field K] (σ : K ≃+* K)
    (k : Roots A) :
    (rootSubgroup A hd hs
      hp ho K k).map
        (unitTwist A hd hs hp ho p hA K σ).toMonoidHom =
      rootSubgroup A hd hs
        hp ho K
        (rootPermutation A p hA k) := by
  let z := rootWitness A hd
    hs hp ho k
  have hw : wordRoot A hs
      hp b₀ s₀ z.val.1
      (negativeIndex A hs
        hp (s₀ z.val.2)) = k := by
    apply Subtype.ext
    rw [← wordLinear_root, negative_val]
    exact z.property.symm
  have he := wordRoot_permutation A hd
    hs hp ho
    p hA z.val.1
    (negativeIndex A hs
      hp (s₀ z.val.2))
  change rootPermutation A p hA
    (wordRoot A hs hp
      b₀ s₀ z.val.1 (negativeIndex A hs
        hp (s₀ z.val.2))) =
    wordRoot A hs hp
      b₀ s₀ (z.val.1.map p)
      (rootPermutation A p hA
        (negativeIndex A hs
          hp (s₀ z.val.2))) at he
  have hsimple : rootPermutation A p hA
      (s₀ z.val.2 : Roots A) =
        (s₀ (p z.val.2) : Roots A) :=
    simple_rootPermutation A hd
      hs hp ho
      p hA z.val.2
  rw [hw, rootPermutation_negative, hsimple] at he
  have hdegree : (rootPermutation A p hA k).val =
      wordLinear A hs hp
        b₀ s₀ (z.val.1.map p) (-(s₀ (p z.val.2) :
          Roots A).val) := by
    rw [congrArg Subtype.val he, ← wordLinear_root, negative_val]
  rw [rootSubgroup_eq_word A hd
      hs hp ho
      K k z.val.1 z.val.2 z.property,
    rootSubgroup_eq_word A hd
      hs hp ho
      K _ (z.val.1.map p) (p z.val.2) hdegree]
  exact word_root_subgroup_twist A hd hs hp ho p hA K σ z.val.1 z.val.2


end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramFieldRootTwist
