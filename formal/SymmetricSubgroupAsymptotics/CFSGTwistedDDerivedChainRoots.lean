import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedPairedRoots
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDChainDoubleCommutators

/-! All untouched positive simple tests lie in the SAME original Derived
action image. Their witnesses are literal double commutators of original
Fixed simple roots, including rank four and the two-element base field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedChainRoots
open CFSG.Models.Chevalley CFSGSerreFixedRootElements CFSGTwistedDFixedA2
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedCentralCocycle
open CFSGTwistedDSingularPrefix CFSGTwistedDFixedChainRoots
open CFSGTwistedDDerivedPairedRoots CFSGOrthogonalDChainDoubleCommutators

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

def testAction (s : ℕ) (q : CFSG.PrimePower) : elementaryRootGroup (q.Extension 2) (s + 4) →*
    ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
      (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
  elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)

def firstWord (s : ℕ) (q : CFSG.PrimePower) (i j : Fin (s + 2)) : Derived s q :=
  derivedCommutator (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) ⁅fixedChainRoot s q false i, fixedChainRoot s q false j⁆
    (fixedChainRoot s q true j)

def secondWord (s : ℕ) (q : CFSG.PrimePower) (i j : Fin (s + 2)) : Derived s q :=
  derivedCommutator (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) (fixedChainRoot s q true i)
    ⁅fixedChainRoot s q false i, fixedChainRoot s q false j⁆

theorem firstWord_coe (s : ℕ) (q : CFSG.PrimePower) (i j : Fin (s + 2)) :
    (firstWord s q i j).val =
      ⁅⁅fixedChainRoot s q false i, fixedChainRoot s q false j⁆,
        fixedChainRoot s q true j⁆ := rfl

theorem secondWord_coe (s : ℕ) (q : CFSG.PrimePower) (i j : Fin (s + 2)) :
    (secondWord s q i j).val =
      ⁅fixedChainRoot s q true i,
        ⁅fixedChainRoot s q false i, fixedChainRoot s q false j⁆⁆ := rfl

set_option maxRecDepth 4096 in
theorem firstWord_image (s : ℕ) (q : CFSG.PrimePower) (i j : Fin (s + 2)) :
    CFSGTwistedDDerivedPairedRoots.derivedImageAction s q (firstWord s q i j) =
      testAction s q
        ⁅⁅CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) i) 1,
            CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) j) 1⁆,
          CFSGTwistedDPairedRootImages.naturalRoot s q true (chainNode (s + 2) j) 1⁆ := by
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  rw [CFSGTwistedDDerivedPairedRoots.derivedImageAction_apply, firstWord_coe]
  rw [map_commutatorElement, map_commutatorElement, fixedChainRoot_image,
    fixedChainRoot_image, fixedChainRoot_image]
  simp only [testAction, map_commutatorElement]
  rfl

set_option maxRecDepth 4096 in
theorem secondWord_image (s : ℕ) (q : CFSG.PrimePower) (i j : Fin (s + 2)) :
    CFSGTwistedDDerivedPairedRoots.derivedImageAction s q (secondWord s q i j) =
      testAction s q
        ⁅CFSGTwistedDPairedRootImages.naturalRoot s q true (chainNode (s + 2) i) 1,
          ⁅CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) i) 1,
            CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) j) 1⁆⁆ := by
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  rw [CFSGTwistedDDerivedPairedRoots.derivedImageAction_apply, secondWord_coe]
  rw [map_commutatorElement, map_commutatorElement, fixedChainRoot_image,
    fixedChainRoot_image, fixedChainRoot_image]
  simp only [testAction, map_commutatorElement]
  rfl

theorem chain_mem_derived_preimage (s : ℕ) (q : CFSG.PrimePower) (i : Fin (s + 2)) :
    CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) i) 1 ∈
      naturalDerivedPreimage s q := by
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  by_cases hi : i.val + 1 < s + 2
  · let j : Fin (s + 2) := ⟨i.val + 1, hi⟩
    have he : CFSGTwistedDFixedChainRoots.nextCoordinate s i = chainNode (s + 2) j := Fin.ext rfl
    have hij : chainNode (s + 2) i ≠ chainNode (s + 2) j := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = i.val + 1 at hv
      omega
    have hik : chainNode (s + 2) i ≠ CFSGTwistedDFixedChainRoots.nextCoordinate s j := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = i.val + 1 + 1 at hv
      omega
    have hnat : ⁅⁅CFSGTwistedDPairedRootImages.naturalRoot s q false
          (chainNode (s + 2) i) 1,
        CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) j) 1⁆,
        CFSGTwistedDPairedRootImages.naturalRoot s q true (chainNode (s + 2) j) 1⁆ =
        CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) i) 1 := by
      rw [CFSGTwistedDFixedChainRoots.naturalRoot_positive,
        CFSGTwistedDFixedChainRoots.naturalRoot_positive,
        CFSGTwistedDFixedChainRoots.naturalRoot_negative]
      simpa only [he] using
        (first_edge (q.Extension 2) (s + 4) _ _ _ hij (chainNode_ne_next s j) hik 1)
    refine ⟨firstWord s q i j, ?_⟩
    exact (firstWord_image s q i j).trans (congrArg ν hnat)
  · have hi0 : 0 < i.val := by have := i.isLt; omega
    let j : Fin (s + 2) := ⟨i.val - 1, by have := i.isLt; omega⟩
    have he : CFSGTwistedDFixedChainRoots.nextCoordinate s j = chainNode (s + 2) i := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    have hji : chainNode (s + 2) j ≠ chainNode (s + 2) i := by
      intro h
      have hv := congrArg Fin.val h
      change i.val - 1 = i.val at hv
      omega
    have hjk : chainNode (s + 2) j ≠ CFSGTwistedDFixedChainRoots.nextCoordinate s i := by
      intro h
      have hv := congrArg Fin.val h
      change i.val - 1 = i.val + 1 at hv
      omega
    have hnat : ⁅CFSGTwistedDPairedRootImages.naturalRoot s q true
          (chainNode (s + 2) j) 1,
        ⁅CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) j) 1,
          CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) i) 1⁆⁆ =
        CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) i) 1 := by
      rw [CFSGTwistedDFixedChainRoots.naturalRoot_negative,
        CFSGTwistedDFixedChainRoots.naturalRoot_positive,
        CFSGTwistedDFixedChainRoots.naturalRoot_positive]
      simpa only [he] using
        (second_edge (q.Extension 2) (s + 4) _ _ _ hji (chainNode_ne_next s i) hjk 1)
    refine ⟨secondWord s q j i, ?_⟩
    exact (secondWord_image s q j i).trans (congrArg ν hnat)

end SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedChainRoots
