import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootTorusConjugation

/-! Literal torus elements and lattice-identity Weyl words normalize
every actual root subgroup, hence both simple-root generated groups.
No identification of the lattice kernel with the torus is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLineNormalizers
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootWeylAction
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateNegativeSimpleRootLine
open CFSGNormTwoCoordinateRootTorusConjugation CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckColumns
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

private theorem mem_normalizer_of_map_eq {G : Type*} [Group G]
    (P : Subgroup G) (g : G)
    (he : P.map (MulAut.conj g).toMonoidHom = P) :
    g ∈ Subgroup.normalizer (P : Set G) := by
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun H : Subgroup G => (H : Set G)) he

theorem rootGroup_eq_iSup_canonical (K : Type) [Field K] (neg : Bool) :
    rootGroup A hs hp b₀ s₀ K neg = ⨆ j, canonicalRootSubgroup D K neg j := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨j,t⟩,rfl⟩
    exact (le_iSup (fun j => canonicalRootSubgroup D K neg j) j)
      (canonicalRoot_mem_subgroup D K neg j t)
  · apply iSup_le
    intro j x hx
    obtain ⟨t,rfl⟩ := hx
    exact Subgroup.subset_closure ⟨(j,t),rfl⟩

theorem rootGroups_normalized_of_root_lines (K : Type) [Field K]
    (g : (Matrix ((b₀).support ⊕ Roots A) ((b₀).support ⊕ Roots A) K)ˣ)
    (hg : ∀ k : Roots A, (rootSubgroup A hd hs hp ho K k).map
      (MulAut.conj g).toMonoidHom = rootSubgroup A hd hs hp ho K k)
    (neg : Bool) : g ∈ Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K neg : Set _) := by
  apply mem_normalizer_of_map_eq
  rw [rootGroup_eq_iSup_canonical A hd hs hp ho K neg, Subgroup.map_iSup]
  congr 1
  funext j
  cases neg
  · simpa only [rootSubgroup_simple_eq_canonical A hd hs hp ho K j] using hg (s₀ j)
  · simpa only [rootSubgroup_negative_simple_eq_canonical A hd hs hp ho K j]
      using hg (negativeIndex A hs hp (s₀ j))

theorem identity_word_root_line (K : Type) [Field K] (w : List (Fin r))
    (hw : wordLinear A hs hp b₀ s₀ w = 1) (k : Roots A) :
    (rootSubgroup A hd hs hp ho K k).map
      (MulAut.conj (CFSGSerreQuadraticWeylWord.canonicalWord D K w)).toMonoidHom =
        rootSubgroup A hd hs hp ho K k := by
  rw [rootSubgroup_map_word]
  congr 1
  apply Subtype.ext
  have he := wordLinear_root A hs hp b₀ s₀ w k
  rw [hw] at he
  exact he.symm

theorem identity_word_normalizes (K : Type) [Field K] (w : List (Fin r))
    (hw : wordLinear A hs hp b₀ s₀ w = 1) (neg : Bool) :
    CFSGSerreQuadraticWeylWord.canonicalWord D K w ∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K neg : Set _) :=
  rootGroups_normalized_of_root_lines A hd hs hp ho K _
    (identity_word_root_line A hd hs hp ho K w hw) neg

theorem parameterTorus_root_line (K : Type) [Field K] (i : Fin r) (t : Kˣ)
    (k : Roots A) : (rootSubgroup A hd hs hp ho K k).map
      (MulAut.conj (parameterTorus A hs hp b₀ s₀ K i t)).toMonoidHom =
        rootSubgroup A hd hs hp ho K k := by
  let c : K := (t : K) ^ (integerPairing A (s₀ i : Roots A).val k.val)
  have hc : c ≠ 0 := zpow_ne_zero _ (Units.ne_zero t)
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨a,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k y).mp hy
    change parameterTorus A hs hp b₀ s₀ K i t * _ *
      (parameterTorus A hs hp b₀ s₀ K i t)⁻¹ ∈ _
    rw [torus_conjugate_selected_root]
    exact selectedRootElement_mem A hd hs hp ho K k _
  · intro hx
    obtain ⟨a,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x).mp hx
    refine ⟨selectedRootElement A hd hs hp ho K k (a/c),
      selectedRootElement_mem A hd hs hp ho K k _,?_⟩
    change parameterTorus A hs hp b₀ s₀ K i t * _ *
      (parameterTorus A hs hp b₀ s₀ K i t)⁻¹ = _
    rw [torus_conjugate_selected_root]
    change selectedRootElement A hd hs hp ho K k ((a/c)*c) = _
    rw [div_mul_cancel₀ a hc]

theorem torusGroup_normalizes (K : Type) [Field K] (neg : Bool) :
    torusGroup A hs hp b₀ s₀ K ≤
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K neg : Set _) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,t⟩,rfl⟩
  exact rootGroups_normalized_of_root_lines A hd hs hp ho K _
    (parameterTorus_root_line A hd hs hp ho K i t) neg

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLineNormalizers
