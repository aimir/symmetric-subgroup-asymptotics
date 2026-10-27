import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPrimitiveFamily
import SymmetricSubgroupAsymptotics.CFSGSerreChevalleyInvolution

/-! Actual Chevalley transport of original integral paths. Path signs
are retained literally; transpose is not asserted to be a Lie map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalChevalleyPaths
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreDividedPowerPaths
open CFSGSerreChevalleyInvolution CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticOriginalCartanTail CFSGSymplecticOriginalPrimitiveFamily
variable (r : ℕ)

theorem map_operator (neg : Bool) (i : Fin r) (k : ℕ) (x : Source r) :
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (integralOperator (CartanMatrix.C r).transpose neg i k x)=
      integralOperator (CartanMatrix.C r).transpose (!neg) i k
        (CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose x) := by
  apply Subtype.ext
  exact rationalMap_dividedPower (CartanMatrix.C r).transpose neg i k x.val

private theorem map_steps (neg : Bool) (ss : List (Fin r×ℕ)) (x : Source r) :
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (applySteps (CartanMatrix.C r).transpose neg ss x)=
      applySteps (CartanMatrix.C r).transpose (!neg) ss
        (CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => simp only [applySteps,ih,map_operator]

private theorem map_pathVector (neg : Bool) (start : Fin r) (ss : List (Fin r×ℕ)) :
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (pathVector (CartanMatrix.C r).transpose neg start ss)=
      pathVector (CartanMatrix.C r).transpose (!neg) start ss := by
  unfold pathVector
  rw [map_steps]
  congr 1
  apply Subtype.ext
  change rationalMap (CartanMatrix.C r).transpose
    (generator (CartanMatrix.C r).transpose (if neg then .F start else .E start))=
      generator (CartanMatrix.C r).transpose (if !neg then .F start else .E start)
  cases neg
  · exact rationalMap_E (CartanMatrix.C r).transpose start
  · exact rationalMap_F (CartanMatrix.C r).transpose start

theorem map_path_positive (start : Fin r) (ss : List (Fin r×ℕ)) :
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (path r false start ss)=
      (-1:ℤ)^(ss.map Prod.snd).sum • path r true start ss := by
  simp only [path,Bool.false_eq_true,if_false,if_true,one_smul,map_pathVector]
  rcases neg_one_pow_eq_or ℤ (ss.map Prod.snd).sum with h | h <;> simp [h]

theorem map_path_negative (start : Fin r) (ss : List (Fin r×ℕ)) :
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (path r true start ss)=
      (-1:ℤ)^(ss.map Prod.snd).sum • path r false start ss := by
  simp only [path,Bool.false_eq_true,if_false,if_true,one_smul,map_smul,map_pathVector,Bool.not_true]

theorem map_root_swap (neg : Bool) (j : RootIndex r) : ∃ z : ℤ,
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (root r neg j)=z • root r (!neg) j := by
  cases neg
  · rcases j with ij | (i | ij)
    · exact ⟨_,map_path_positive r _ _⟩
    · exact ⟨_,map_path_positive r _ _⟩
    · exact ⟨_,map_path_positive r _ _⟩
  · rcases j with ij | (i | ij)
    · exact ⟨_,map_path_negative r _ _⟩
    · exact ⟨_,map_path_negative r _ _⟩
    · exact ⟨_,map_path_negative r _ _⟩

theorem map_root_mem (neg : Bool) (j : RootIndex r) :
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (root r neg j)∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  obtain ⟨z,hz⟩:=map_root_swap r neg j
  rw [hz]
  exact Submodule.smul_mem _ z (Submodule.subset_span ⟨.inr (!neg,j),rfl⟩)

private theorem map_Hnat (a : ℕ) :
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (Hnat r a)= -Hnat r a := by
  unfold Hnat
  split_ifs with h
  · apply Subtype.ext
    exact rationalMap_H (CartanMatrix.C r).transpose ⟨a,h⟩
  · simp

theorem map_tail (a : ℕ) :
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (tail r a)= -tail r a := by
  unfold tail
  rw [map_sum]
  simp_rw [map_Hnat]
  simp only [Finset.sum_neg_distrib]

theorem map_mem (x : Source r)
    (hx : x∈Submodule.span ℤ (Set.range (primitiveVector r))) :
    CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose x∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩:=hx
    rcases j with i | ⟨neg,j⟩
    · change CFSGSerreChevalleyInvolution.integralMap (CartanMatrix.C r).transpose (tail r i.val)∈_
      rw [map_tail]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨.inl i,rfl⟩)
    · exact map_root_mem r neg j
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul z x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ z hx

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalChevalleyPaths
