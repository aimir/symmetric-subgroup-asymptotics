import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice
import Mathlib.Tactic.NormNum

/-! Exact integral spanning from cubic adjoint tables. An integral
half-square certificate, rather than rational invariance alone, proves
stability under every original divided power. The final equality uses
the defining minimality of the SAME original integral Serre lattice.
No dimension, independence or tensor faithfulness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreIntegralCubicFamilySpan
open CFSG.Models.Chevalley CFSGSerreDiagram

theorem normalized_power_mem {V:Type*} [AddCommGroup V] [Module ℚ V]
    (S:Submodule ℤ V) (D:Module.End ℚ V) (x:V) (hx:x∈S) (hfirst:D x∈S)
    (hhalf:∃y∈S,(D^2) x=(2:ℚ) • y) (hthree:(D^3) x=0) (k:ℕ) :
    ((k.factorial:ℚ)⁻¹) • (D^k) x∈S := by
  by_cases hk0:k=0
  · subst k
    simpa only [Nat.factorial_zero,Nat.cast_one,inv_one,pow_zero,
      Module.End.one_apply,one_smul] using hx
  by_cases hk1:k=1
  · subst k
    simpa only [Nat.factorial_one,Nat.cast_one,inv_one,pow_one,one_smul] using hfirst
  by_cases hk2:k=2
  · subst k
    obtain ⟨y,hy,he⟩:=hhalf
    have hs:((Nat.factorial 2:ℚ)⁻¹)*(2:ℚ)=1:=by norm_num
    rw [he,smul_smul,hs,one_smul]
    exact hy
  have hk:3≤k:=by omega
  obtain ⟨m,hm⟩:∃m:ℕ,k=m+3:=⟨k-3,by omega⟩
  have hp:(D^k) x=0 := by
    rw [hm,pow_add,Module.End.mul_apply,hthree,map_zero]
  rw [hp,smul_zero]
  exact S.zero_mem

variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ) {J:Type*}

theorem integralLattice_eq_span_of_cubic_family (v:J→integralLattice A)
    (hgen:∀g,generator A g∈Submodule.span ℤ (Set.range (fun j=>(v j).val)))
    (hfirst:∀neg i j,
      ⁅rootVector A neg i,(v j).val⁆∈Submodule.span ℤ (Set.range (fun j=>(v j).val)))
    (hhalf:∀neg i j,∃y∈Submodule.span ℤ (Set.range (fun j=>(v j).val)),
      ((LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i))^2) (v j).val=(2:ℚ) • y)
    (hthree:∀neg i j,
      ((LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i))^3) (v j).val=0) :
    integralLattice A=Submodule.span ℤ (Set.range (fun j=>(v j).val)) := by
  let S:Submodule ℤ (RationalLie A):=Submodule.span ℤ (Set.range (fun j=>(v j).val))
  apply le_antisymm
  · apply integralLattice_le_of_stable A S hgen
    intro neg i k x hx
    induction hx using Submodule.span_induction with
    | mem x hx=>
      obtain ⟨j,rfl⟩:=hx
      change ((k.factorial:ℚ)⁻¹) •
        ((LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i))^k) (v j).val∈S
      exact normalized_power_mem S _ _ (Submodule.subset_span ⟨j,rfl⟩)
        (hfirst neg i j) (hhalf neg i j) (hthree neg i j) k
    | zero=>rw [map_zero];exact S.zero_mem
    | add x y _ _ hx hy=>rw [map_add];exact S.add_mem hx hy
    | smul c x _ hx=>rw [map_smul];exact S.smul_mem c hx
  · apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    exact (v j).property

end SymmetricSubgroupAsymptotics.CFSGSerreIntegralCubicFamilySpan
