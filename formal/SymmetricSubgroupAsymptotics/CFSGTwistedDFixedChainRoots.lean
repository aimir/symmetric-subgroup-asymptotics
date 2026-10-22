import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedRootImages
import SymmetricSubgroupAsymptotics.CFSGTwistedDA2MatrixWitness
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPrefix

/-! Every untouched chain node gives an actual ORIGINAL Fixed root.
Its natural image is the literal SL-chain element at the same coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainRoots
open CFSG.Models.Chevalley CFSGSerreOrdinaryTwists CFSGSerreFixedRootElements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGTwistedDFixedA2 CFSGTwistedDSingularPrefix CFSGTwistedDA2MatrixWitness

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

def nextCoordinate (s : ℕ) (i : Fin (s + 2)) : Fin (s + 4) :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

theorem chainNode_ne_next (s : ℕ) (i : Fin (s + 2)) :
    chainNode (s + 2) i ≠ nextCoordinate s i := by
  intro h
  have hh := congrArg Fin.val h
  change i.val = i.val + 1 at hh
  omega

theorem chainNode_fixed (s : ℕ) (i : Fin (s + 2)) :
    CFSG.Models.dTwist (chainNode (s + 2) i) = chainNode (s + 2) i := by
  have hi := i.isLt
  have h2 : 2 ≤ s + 4 := by omega
  have ha : (chainNode (s + 2) i).val ≠ (s + 4) - 2 := by
    dsimp only [chainNode]
    omega
  have hb : (chainNode (s + 2) i).val ≠ (s + 4) - 1 := by
    dsimp only [chainNode]
    omega
  simp only [CFSG.Models.dTwist, dif_pos h2, if_neg ha, if_neg hb]

def fixedChainRoot (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (i : Fin (s + 2)) :
    Fixed s q :=
  fixedRoot (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) neg (chainNode (s + 2) i) 1 (chainNode_fixed s i) (one_pow _)

theorem fixedChainRoot_image (s : ℕ) (q : CFSG.PrimePower) (neg : Bool)
    (i : Fin (s + 2)) :
    CFSGTwistedDFixedCentralCocycle.fixedImageAction s q (fixedChainRoot s q neg i) =
      elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
        (CFSGTwistedDPairedRootImages.naturalRoot s q neg (chainNode (s + 2) i) 1) :=
  CFSGTwistedDPairedRootImages.root_image s q neg (chainNode (s + 2) i) 1

theorem naturalRoot_positive (s : ℕ) (q : CFSG.PrimePower) (i : Fin (s + 2)) :
    CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) i) 1 =
      chain (q.Extension 2) (s + 4) (chainNode (s + 2) i) (nextCoordinate s i)
        (chainNode_ne_next s i) 1 := by
  have hi : (chainNode (s + 2) i).val + 1 < s + 4 := by
    have := i.isLt
    dsimp only [chainNode]
    omega
  apply Subtype.ext
  apply Units.ext
  change 1 + (1 : q.Extension 2) • positive (q.Extension 2) (s + 4) (chainNode (s + 2) i) =
    (doubleHom (q.Extension 2) (s + 4)
      (CFSGTypeAElementaryMatrices.elementary (chainNode_ne_next s i) 1) :
        Mat (q.Extension 2) (s + 4))
  rw [doubleHom_elementary_val, positive, dif_pos hi] <;> rfl

theorem naturalRoot_negative (s : ℕ) (q : CFSG.PrimePower) (i : Fin (s + 2)) :
    CFSGTwistedDPairedRootImages.naturalRoot s q true (chainNode (s + 2) i) 1 =
      chain (q.Extension 2) (s + 4) (nextCoordinate s i) (chainNode (s + 2) i)
        (Ne.symm (chainNode_ne_next s i)) 1 := by
  have hi : (chainNode (s + 2) i).val + 1 < s + 4 := by
    have := i.isLt
    dsimp only [chainNode]
    omega
  apply Subtype.ext
  apply Units.ext
  change 1 + (1 : q.Extension 2) • negative (q.Extension 2) (s + 4) (chainNode (s + 2) i) =
    (doubleHom (q.Extension 2) (s + 4)
      (CFSGTypeAElementaryMatrices.elementary (Ne.symm (chainNode_ne_next s i)) 1) :
        Mat (q.Extension 2) (s + 4))
  rw [doubleHom_elementary_val, negative, positive, dif_pos hi]
  simp only [Matrix.transpose_sub, Matrix.transpose_single, chainMatrix] <;> rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainRoots
