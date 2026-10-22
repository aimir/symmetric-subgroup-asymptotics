import SymmetricSubgroupAsymptotics.CFSGTwistedDImageCommutators

/-! Full field-fixed parameters at untouched natural D-chain nodes.
The source membership is in the actual original Fixed image; the natural
matrices retain precisely the original SL-chain parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainParameters
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGTwistedDSingularPrefix CFSGTwistedDFixedChainRoots
open CFSGTwistedDA2MatrixWitness CFSGTwistedDImageCommutators

theorem parameter_mem_fixed_preimage (s : ℕ) (q : CFSG.PrimePower) (neg : Bool)
    (i : Fin (s + 2)) (t : q.Extension 2)
    (ht : CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 t = t) :
    CFSGTwistedDPairedRootImages.naturalRoot s q neg (chainNode (s + 2) i) t ∈
      CFSGTwistedDFixedCentralCocycle.naturalFixedPreimage s q :=
  fixed_node_root_mem_preimage s q neg _ (chainNode_fixed s i) t ht

theorem positive_parameter (s : ℕ) (q : CFSG.PrimePower) (i : Fin (s + 2))
    (t : q.Extension 2) :
    CFSGTwistedDPairedRootImages.naturalRoot s q false (chainNode (s + 2) i) t =
      chain (q.Extension 2) (s + 4) (chainNode (s + 2) i)
        (CFSGTwistedDFixedChainRoots.nextCoordinate s i) (chainNode_ne_next s i) t := by
  have hi : (chainNode (s + 2) i).val + 1 < s + 4 := by
    have := i.isLt
    dsimp only [chainNode]
    omega
  apply Subtype.ext
  apply Units.ext
  change 1 + t • positive (q.Extension 2) (s + 4) (chainNode (s + 2) i) =
    (doubleHom (q.Extension 2) (s + 4)
      (CFSGTypeAElementaryMatrices.elementary (chainNode_ne_next s i) t) :
        Mat (q.Extension 2) (s + 4))
  rw [doubleHom_elementary_val, positive, dif_pos hi] <;> rfl

theorem negative_parameter (s : ℕ) (q : CFSG.PrimePower) (i : Fin (s + 2))
    (t : q.Extension 2) :
    CFSGTwistedDPairedRootImages.naturalRoot s q true (chainNode (s + 2) i) t =
      chain (q.Extension 2) (s + 4) (CFSGTwistedDFixedChainRoots.nextCoordinate s i)
        (chainNode (s + 2) i) (Ne.symm (chainNode_ne_next s i)) t := by
  have hi : (chainNode (s + 2) i).val + 1 < s + 4 := by
    have := i.isLt
    dsimp only [chainNode]
    omega
  apply Subtype.ext
  apply Units.ext
  change 1 + t • negative (q.Extension 2) (s + 4) (chainNode (s + 2) i) =
    (doubleHom (q.Extension 2) (s + 4)
      (CFSGTypeAElementaryMatrices.elementary (Ne.symm (chainNode_ne_next s i)) t) :
        Mat (q.Extension 2) (s + 4))
  rw [doubleHom_elementary_val, negative, positive, dif_pos hi]
  simp only [Matrix.transpose_sub, Matrix.transpose_single, chainMatrix] <;> rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainParameters
