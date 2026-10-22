import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootDichotomy
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleGaussFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementTorus
import SymmetricSubgroupAsymptotics.CFSGSimpleBruhatMultiplication

/-! An actual whole-group Bruhat COVER for the original coordinate Geck
group, indexed by literal Weyl words. Every local factorization and root
sign condition is supplied from the actual matrices. No uniqueness of
representatives, group recognition, or global normalizer claim is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatCover
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylUnits
open CFSGNormTwoCoordinateRootDichotomy CFSGNormTwoGeckWeylWordTorus
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckPositiveComplement
open CFSGNormTwoGeckComplementNormalizer CFSGNormTwoGeckSimpleGaussFactor
open CFSGNormTwoGeckSimpleRootCells CFSGNormTwoGeckWeylSquareTorus
open CFSGSerreQuadraticMatrix CFSGWeylWordBruhatCover
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem wordValue_eq_wordUnit (K : Type) [Field K] (w : List (Fin r)) :
    wordValue (fun i=>canonicalWeyl (realizationData A hs hp b₀ s₀) K i) w=
      wordUnit A hs hp b₀ s₀ K w := by
  induction w with
  | nil=>rfl
  | cons i w ih=>simp only [wordValue,wordUnit,ih]

theorem left_simple_word_cells (K : Type) [Field K] (i : Fin r) (w : List (Fin r))
    (b : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hb : b∈borelEnvelope A hs hp b₀ s₀ K) :
    WordCells (borelEnvelope A hs hp b₀ s₀ K)
      (fun j=>canonicalWeyl (realizationData A hs hp b₀ s₀) K j)
      (canonicalWeyl (realizationData A hs hp b₀ s₀) K i*b*
        wordValue (fun j=>canonicalWeyl (realizationData A hs hp b₀ s₀) K j) w) := by
  rw [wordValue_eq_wordUnit]
  have hUB : rootGroup A hs hp b₀ s₀ K false≤borelEnvelope A hs hp b₀ s₀ K := le_sup_left
  have hTB : torusGroup A hs hp b₀ s₀ K≤borelEnvelope A hs hp b₀ s₀ K := le_sup_right
  have hh := CFSGSimpleBruhatMultiplication.left_simple_cell
    (borelEnvelope A hs hp b₀ s₀ K) (rootGroup A hs hp b₀ s₀ K false)
    (torusGroup A hs hp b₀ s₀ K) (positiveComplement A hs hp b₀ s₀ K i)
    (canonicalWeyl (realizationData A hs hp b₀ s₀) K i) (wordUnit A hs hp b₀ s₀ K w) b
    (canonicalRoot (realizationData A hs hp b₀ s₀) K false i)
    (canonicalRoot (realizationData A hs hp b₀ s₀) K true i) hUB hTB
    (CFSGNormTwoGeckComplementTorus.borel_factor A hs hp b₀ s₀ K i b hb)
    (fun v hv=>hUB (complement_le_positive A hs hp b₀ s₀ K i
      (weyl_conjugate_mem A hs hp b₀ s₀ K i v hv)))
    (word_inverse_torus_mem A hs hp b₀ s₀ K w)
    (conjugate_root_dichotomy A hd hs hp ho K w i)
    (canonicalRoot_zero _ K false i) (weyl_positive_nonzero_factor A hs hp b₀ s₀ K i)
  rcases hh with h|h
  · refine ⟨i::w,?_⟩
    simpa only [wordValue,wordValue_eq_wordUnit] using h
  · refine ⟨w,?_⟩
    simpa only [wordValue_eq_wordUnit] using h

theorem canonical_bruhat_cover (K : Type) [Field K]
    (g : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hg : g∈canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K) :
    ∃w : List (Fin r),∃b∈borelEnvelope A hs hp b₀ s₀ K,
      ∃c∈borelEnvelope A hs hp b₀ s₀ K,g=b*wordUnit A hs hp b₀ s₀ K w*c := by
  have hgen : Subgroup.closure
      ((borelEnvelope A hs hp b₀ s₀ K : Set _)∪
        Set.range (fun i : Fin r=>canonicalWeyl (realizationData A hs hp b₀ s₀) K i))=
      canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K := by
    simpa only [parameterWeyl_one] using borel_simple_weyls_generate A hs hp b₀ s₀ K
  have hgc : g∈Subgroup.closure
      ((borelEnvelope A hs hp b₀ s₀ K : Set _)∪
        Set.range (fun i : Fin r=>canonicalWeyl (realizationData A hs hp b₀ s₀) K i)) := by
    rw [hgen]
    exact hg
  have hh := closure_le_wordCells (borelEnvelope A hs hp b₀ s₀ K)
    (fun i=>canonicalWeyl (realizationData A hs hp b₀ s₀) K i)
    (weyl_four A hs hp b₀ s₀ K) (left_simple_word_cells A hd hs hp ho K) g hgc
  obtain ⟨w,b,hb,c,hc,he⟩ := hh
  exact ⟨w,b,hb,c,hc,by simpa only [wordValue_eq_wordUnit] using he⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatCover
