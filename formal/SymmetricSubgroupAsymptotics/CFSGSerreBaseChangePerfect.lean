import SymmetricSubgroupAsymptotics.CFSGSerreIntegralPerfect

/-! Perfectness of the same integral Serre lattice survives every field
extension, including bad characteristics. The minus-one column condition
is explicit; it holds for simply-laced connected diagrams of rank≥2. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreBaseChangePerfect
open CFSG.Models.Chevalley CFSGSerreIntegralLieAlgebra
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

def bracketSpan : Submodule K (Space A K) :=
  Submodule.span K (Set.range (fun xy : Space A K × Space A K => ⁅xy.1,xy.2⁆))

private theorem tmul_mem (a : K) (x : integralLattice A)
    (hx : x ∈ CFSGSerreIntegralPerfect.bracketSpan A) :
    a ⊗ₜ[ℤ] x ∈ bracketSpan A K := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨u,v⟩,rfl⟩ := hz
    have h : ⁅a ⊗ₜ[ℤ] u,(1 : K) ⊗ₜ[ℤ] v⁆ ∈ bracketSpan A K :=
      Submodule.subset_span ⟨(a ⊗ₜ[ℤ] u,(1 : K) ⊗ₜ[ℤ] v),rfl⟩
    simpa only [spaceBracket_tmul, mul_one] using h
  | zero => simpa only [TensorProduct.tmul_zero] using (bracketSpan A K).zero_mem
  | add x y _ _ hx hy =>
    rw [TensorProduct.tmul_add]
    exact (bracketSpan A K).add_mem hx hy
  | smul z x _ hx =>
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have he : z • a = (z : K) • a := by
      simp only [int_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rw [he]
    exact (bracketSpan A K).smul_mem (z : K) hx

theorem bracketSpan_eq_top
    (hneighbour : ∀ i : Fin r, ∃ j : Fin r, A j i = -1) : bracketSpan A K = ⊤ := by
  have hs := CFSGSerreIntegralPerfect.bracketSpan_eq_top A hneighbour
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact (bracketSpan A K).zero_mem
  | tmul a u =>
    apply tmul_mem A K a u
    rw [hs]
    trivial
  | add x y hx hy => exact (bracketSpan A K).add_mem hx hy

end SymmetricSubgroupAsymptotics.CFSGSerreBaseChangePerfect
