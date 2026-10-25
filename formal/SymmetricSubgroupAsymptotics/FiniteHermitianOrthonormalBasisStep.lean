import SymmetricSubgroupAsymptotics.FiniteHermitianUnitPerp
import Mathlib.LinearAlgebra.Basis.Fin

/-! Prepend an actual unit vector to an orthonormal basis of its
perpendicular subspace inside the SAME ambient subspace. The basis
constructor is Mathlib's checked codimension-one basis gluing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalBasisStep
open Module CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
open FiniteHermitianUnitPerp

theorem exists_basis_step {K I : Type*} [Field K] [Fintype I]
    (sigma : K ≃+* K) (H : Matrix I I K)
    (W : Submodule K (I → K)) (v : I → K)
    (hv : v ∈ W) (hone : hermitianPair sigma H v v=1)
    (hswap : ∀ x y, hermitianPair sigma H x y=0 ↔ hermitianPair sigma H y x=0)
    {n : ℕ} (b : Basis (Fin n) K (unitPerp sigma H W v))
    (hb : ∀ i j, hermitianPair sigma H (b i).val (b j).val=if i=j then 1 else 0) :
    ∃ B : Basis (Fin (n+1)) K W,
      ∀ i j, hermitianPair sigma H (B i).val (B j).val=if i=j then 1 else 0 := by
  classical
  let P := unitPerp sigma H W v
  have hPW : P ≤ W := inf_le_left
  let phi := pairRightLinear sigma H v
  have hli : ∀ (a : K), ∀ x ∈ P, a • v+x=0 → a=0 := by
    intro a x hx he
    have hz : hermitianPair sigma H v x=0 := hx.2
    have hh := congrArg phi he
    rw [map_add,map_smul,map_zero] at hh
    change a*hermitianPair sigma H v v+hermitianPair sigma H v x=0 at hh
    simpa only [hone,hz,mul_one,add_zero] using hh
  have hsp : ∀ x ∈ W, ∃ a : K, x+a • v ∈ P := by
    intro x hx
    refine ⟨-hermitianPair sigma H v x,?_⟩
    refine ⟨W.add_mem hx (W.smul_mem _ hv),?_⟩
    change phi (x+(-hermitianPair sigma H v x) • v)=0
    rw [map_add,map_smul]
    change hermitianPair sigma H v x+
      (-hermitianPair sigma H v x)*hermitianPair sigma H v v=0
    rw [hone,mul_one,add_neg_cancel]
  let B : Basis (Fin (n+1)) K W := Basis.mkFinConsOfLE v hv b hPW hli hsp
  have hB : (B : Fin (n+1) → W)=
      Fin.cons ⟨v,hv⟩ (Submodule.inclusion hPW ∘ b) :=
    Basis.coe_mkFinConsOfLE v hv b hPW hli hsp
  have hB0 : (B 0).val=v := by
    exact congrArg (fun f : Fin (n+1) → W => (f 0).val) hB
  have hBs (i : Fin n) : (B i.succ).val=(b i).val := by
    exact congrArg (fun f : Fin (n+1) → W => (f i.succ).val) hB
  refine ⟨B,?_⟩
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [hB0,if_pos rfl] using hone
    · rw [hB0,hBs,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      exact (b j).property.2
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [hBs,hB0,if_neg (Fin.succ_ne_zero _)]
      exact (hswap v (b i).val).mp (b i).property.2
    · simpa only [hBs,Fin.succ_inj] using hb i j

end SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalBasisStep
