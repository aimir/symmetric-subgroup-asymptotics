import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingAutomorphism
import SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateHyperplanes

/-! The actual original positive complements ARE the coordinate kernels
in its genuine abelianization. Thus its actual axis permutation also
permutes these literal subgroup complements. No parabolic recognition
or literal root lifting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementAction
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateDerivedFirstLayer CFSGNormTwoCoordinateRootLeadingAxes
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinatePositiveQuotientInjectivity
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoCoordinateOriginalLeadingHom CFSGNormTwoCoordinateOriginalLeadingAutomorphism
open CFSGNormTwoCoordinateComplementKernel CFSGNormTwoGeckPositiveComplement
open CFSGSimpleCoordinateAxes CFSGSimpleCoordinateHyperplanes

def originalComplement (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Subgroup (originalPositive A hd hs hp ho K i) :=
  ((positiveComplement A hs hp b₀ s₀ K j).subgroupOf (PositiveGroup A hd hs hp ho K)).map
    (originalPositiveEquiv A hd hs hp ho K p i).toMonoidHom

theorem mem_originalComplement_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r)
    (u : originalPositive A hd hs hp ho K i) :
    u∈originalComplement A hd hs hp ho K p i j↔
      (originalLeadingHom A hd hs hp ho K p i u).toAdd j=0 := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    change (originalLeadingHom A hd hs hp ho K p i
      ((originalPositiveEquiv A hd hs hp ho K p i) v)).toAdd j=0
    rw [originalLeadingHom_equiv_apply]
    exact (positive_mem_complement_iff_leading_zero A hd hs hp ho K j v).mp hv
  · intro hu
    let e := originalPositiveEquiv A hd hs hp ho K p i
    have hv : (e.symm u).val∈positiveComplement A hs hp b₀ s₀ K j := by
      apply (positive_mem_complement_iff_leading_zero A hd hs hp ho K j (e.symm u)).mpr
      exact hu
    exact ⟨e.symm u,hv,e.apply_symm_apply u⟩

theorem originalComplement_map_positiveAut (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (originalPositive A hd hs hp ho K i)) (σ : Equiv.Perm (Fin r))
    (hσ : ∀j : Fin r,(axis (K:=K) j).map
      (originalLeadingAut A hd hs hp ho K p i f).toMonoidHom=axis (K:=K) (σ j)) (j : Fin r) :
    (originalComplement A hd hs hp ho K p i j).map f.toMonoidHom=
      originalComplement A hd hs hp ho K p i (σ j) := by
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨u,hu,rfl⟩
    apply (mem_originalComplement_iff A hd hs hp ho K p i (σ j) (f u)).mpr
    rw [←originalLeadingAut_apply A hd hs hp ho K p i f u]
    exact (coordinate_zero_iff (originalLeadingAut A hd hs hp ho K p i f) σ hσ j
      (originalLeadingHom A hd hs hp ho K p i u)).mpr
      ((mem_originalComplement_iff A hd hs hp ho K p i j u).mp hu)
  · intro hx
    refine ⟨f.symm x,?_,f.apply_symm_apply x⟩
    apply (mem_originalComplement_iff A hd hs hp ho K p i j (f.symm x)).mpr
    apply (coordinate_zero_iff (originalLeadingAut A hd hs hp ho K p i f) σ hσ j
      (originalLeadingHom A hd hs hp ho K p i (f.symm x))).mp
    rw [originalLeadingAut_apply,MulEquiv.apply_symm_apply]
    exact (mem_originalComplement_iff A hd hs hp ho K p i (σ j) x).mp hx

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementAction
