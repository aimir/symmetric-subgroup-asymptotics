import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalFlagIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeRootContainment
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction
import SymmetricSubgroupAsymptotics.CFSGNonpositiveCoordinateCone
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! A zero-functional positive root has nonpositive word image whenever
its supported simple columns do. Thus the opposite weak flag recognizes
a subgroup of the literal word-inversion group, without a root census
or a selected-root sign convention. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalInversion
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckIntegralWord
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateZeroFunctionalSupport
open CFSGNormTwoCoordinateFunctionalFlagIntersection CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootWeylAction CFSGNormTwoCoordinateNegativeRootContainment
open CFSGNonpositiveCoordinateCone CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
open CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

variable (f : (Fin r→ℤ)→ₗ[ℤ]ℤ) (S : Set (Fin r)) (w : List (Fin r))
    (hsupport : ∀k : PositiveRoot A,f k.val.val=0→∀i,k.val.val i≠0→i∈S)
    (hcolumns : ∀i : Fin r,i∈S→∀j : Fin r,
      (latticeWord A w*ᵥ(Pi.single i (1:ℤ) : Fin r→ℤ)) j≤0)

include hsupport hcolumns in
omit [(rootPairing A hs hp).IsReduced] in
theorem zero_root_word_nonpositive (k : PositiveRoot A) (hk : f k.val.val=0) :
    ∀j,(wordRoot A hs hp b₀ s₀ w k.val).val j≤0 := by
  have hc (i : Fin r) (hi : k.val.val i≠0) :
      ∀j,wordLinear A hs hp b₀ s₀ w (Pi.single i (1:ℤ)) j≤0 := by
    have he := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho w)
      (Pi.single i (1:ℤ) : Fin r→ℤ)
    change latticeWord A w*ᵥ(Pi.single i (1:ℤ) : Fin r→ℤ)=
      wordLinear A hs hp b₀ s₀ w (Pi.single i (1:ℤ)) at he
    rw [←he]
    exact hcolumns i (hsupport k hk i hi)
  have hn := linearMap_nonpositive_of_support_columns
    (wordLinear A hs hp b₀ s₀ w).toLinearMap k.val.val k.property hc
  rw [←wordLinear_root A hs hp b₀ s₀ w k.val]
  exact hn

include hsupport hcolumns in
theorem zeroFunctionalGroup_le_negative_comap (K : Type) [Field K] :
    zeroFunctionalGroup A hd hs hp ho K f≤
      (rootGroup A hs hp b₀ s₀ K true).comap
        (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k,hk,a,rfl⟩
  have hm : (MulAut.conj (wordUnit A hs hp b₀ s₀ K w))
      (selectedRootElement A hd hs hp ho K k.val a)∈
        (rootSubgroup A hd hs hp ho K k.val).map
          (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom :=
    ⟨_,selectedRootElement_mem A hd hs hp ho K k.val a,rfl⟩
  have hmap : (rootSubgroup A hd hs hp ho K k.val).map
      (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom=
        rootSubgroup A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k.val) := by
    rw [word_eq_canonicalWord]
    exact rootSubgroup_map_word A hd hs hp ho K w k.val
  rw [hmap] at hm
  exact negative_root_subgroup_le A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k.val)
    (zero_root_word_nonpositive A hd hs hp ho f S w hsupport hcolumns k hk) hm

include hsupport hcolumns in
theorem positive_inf_flag_le_inversion (K : Type) [Field K]
    (hf : ∀k : PositiveRoot A,0≤f k.val.val) :
    rootGroup A hs hp b₀ s₀ K false⊓
      triangularUnits (fun j=>f (latticeWeight A hs hp b₀ j))≤
        rootGroup A hs hp b₀ s₀ K false⊓
          (rootGroup A hs hp b₀ s₀ K true).comap
            (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom := by
  apply le_inf inf_le_left
  exact (positive_inf_functional_flag_eq_zeroFunctionalGroup A hd hs hp ho K f hf).le.trans
    (zeroFunctionalGroup_le_negative_comap A hd hs hp ho f S w hsupport hcolumns K)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalInversion
