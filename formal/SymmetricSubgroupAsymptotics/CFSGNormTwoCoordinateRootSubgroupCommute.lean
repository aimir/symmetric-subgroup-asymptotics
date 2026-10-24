import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPairCommute
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction

/-! Pairing zero or one makes the two actual root subgroups commute.
The Weyl-word membership statement retains the same lattice root label;
there is no choice of a new root parametrization in its conclusion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroupCommute
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateRootWeylAction
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem rootSubgroup_pair_commute (K : Type) [Field K] (k l : Roots A)
    (hpair : integerPairing A k.val l.val=0 ∨ integerPairing A k.val l.val=1)
    (x y : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hx : x∈rootSubgroup A hd hs hp ho K k)
    (hy : y∈rootSubgroup A hd hs hp ho K l) : Commute x y := by
  obtain ⟨a,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x).mp hx
  obtain ⟨b,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K l y).mp hy
  exact CFSGNormTwoCoordinateRootPairCommute.pair_commute A hd hs hp ho K k l hpair a b

theorem canonicalRoot_mem_rootSubgroup (K : Type) [Field K] (j : Fin r) (t : K) :
    canonicalRoot D K false j t∈rootSubgroup A hd hs hp ho K (s₀ j) := by
  rw [rootSubgroup_simple_eq_canonical A hd hs hp ho K j]
  exact ⟨t,rfl⟩

theorem positive_word_mem_rootSubgroup (K : Type) [Field K] (w : List (Fin r))
    (j : Fin r) (t : K) :
    canonicalWord D K w*canonicalRoot D K false j t*(canonicalWord D K w)⁻¹∈
      rootSubgroup A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w (s₀ j)) := by
  rw [←rootSubgroup_map_word A hd hs hp ho K w (s₀ j)]
  exact ⟨canonicalRoot D K false j t,
    canonicalRoot_mem_rootSubgroup A hd hs hp ho K j t,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroupCommute
