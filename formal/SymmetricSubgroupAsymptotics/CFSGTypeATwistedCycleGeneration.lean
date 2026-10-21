import SymmetricSubgroupAsymptotics.CFSGTypeADiagonalRootAction
import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialCycleGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeARootTorus
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare
import SymmetricSubgroupAsymptotics.CFSGRootSubgroupExtraction

/-! The actual torus/twisted-cycle generating pair in every dimension
at least three over a finite field of cardinality at least four. All
monomial row weights, original coordinate indices, and root parameters
are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeATwistedCycleGeneration
open Matrix CFSGTypeAElementaryMatrices CFSGTypeARootTorus
open CFSGTypeADiagonalRootAction CFSGTypeAMonomialMatrices
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F] [Finite F]

theorem eq_top_of_twisted_cycle (hn : 3≤Fintype.card n) (hcard : 4≤Nat.card F)
    (σ : Equiv.Perm n) (hσ : σ.IsCycleOn (Finset.univ : Finset n))
    (W : SL (n:=n) (F:=F)) (d : n→F) (hW : W.val=monomial σ d)
    (hd : ∀ k,d k≠0) (i : n) (g : Fˣ) (hg : ∀ u : Fˣ,u∈Subgroup.zpowers g)
    (hi : i≠σ.symm i) (H : Subgroup (SL (n:=n) (F:=F)))
    (hT : torus hi g∈H) (hS : elementary hi 1*W∈H) : H=⊤ := by
  let j := σ.symm i
  let h : SL (n:=n) (F:=F) := torus hi g
  let D : n→F := fun r => if r=i then (g : F) else if r=j then (g : F)⁻¹ else 1
  have hval : h.val=Matrix.diagonal D := torus_coe hi g
  have hnear : ∀ k : ℕ,0<k→k<Fintype.card n→(σ^k) i≠i := by
    intro k hk hkn he
    have hh := (hσ.pow_apply_eq (Finset.mem_univ i)).mp he
    rw [Finset.card_univ] at hh
    exact Nat.not_dvd_of_pos_of_lt hk hkn hh
  have hσi : σ i≠i := by simpa only [pow_one] using hnear 1 (by decide) (by omega)
  have hσij : σ i≠j := by
    intro he
    have hh := congrArg σ he
    apply hnear 2 (by decide) (by omega)
    simpa only [pow_two,Equiv.Perm.mul_apply,j,σ.apply_symm_apply] using hh
  have hσj : σ j=i := σ.apply_symm_apply i
  have hDi : (D∘σ) i=1 := by simp only [Function.comp_apply,D,if_neg hσi,if_neg hσij]
  have hDj : (D∘σ) j=(g : F) := by simp only [Function.comp_apply,hσj,D,ite_true]
  let k : F := (g : F)^2
  let l : F := (g : F)⁻¹
  have hScale : ∀ a : F,h*elementary hi a*h⁻¹=elementary hi (k*a) :=
    fun a => torus_conjugation hi g a
  have hScale' : ∀ a : F,(W*h*W⁻¹)*elementary hi a*(W*h*W⁻¹)⁻¹=
      elementary hi (l*a) := by
    intro a
    have ha := diagonal_conjugation (W*h*W⁻¹) (D∘σ)
      (monomial_conjugate_diagonal W h σ d D hW hval) hi a
      (show (D∘σ) j≠0 by rw [hDj];exact Units.ne_zero g)
    have he : (D∘σ) i*a/(D∘σ) j=l*a := by rw [hDi,hDj];simp [l,div_eq_mul_inv,mul_comm]
    change (W*h*W⁻¹)*elementary hi a*(W*h*W⁻¹)⁻¹=
      elementary hi ((D∘σ) i*a/(D∘σ) j) at ha
    rw [he] at ha
    exact ha
  have hComm : Commute (W*h*W⁻¹) h :=
    monomial_conjugate_commutes W h σ d D hW hval
  have hk : k≠1 := CFSGTypeAPrimitiveUnitSquare.square_ne_one hcard g hg
  have hl : l≠1 := by
    intro he
    have he' : (g : F)=1 := by
      have hh := congrArg (fun a : F => a⁻¹) he
      simpa only [l,inv_inv,inv_one] using hh
    exact hk (by simp [k,he'])
  let m : F := (1-l)*(1-k)
  have hm : m≠0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hl))
    (sub_ne_zero.mpr (Ne.symm hk))
  have hM : elementary hi m∈H :=
    CFSGRootSubgroupExtraction.root_mem_of_twisted_torus (elementary hi)
      (elementary_add hi) (elementary_zero hi) h W k l hScale hScale' hComm H hT hS
  have hRoot : ∀ a : F,elementary hi a∈H :=
    all_parameters_of_torus H hi g hg hT m hm hM
  have hHW : W∈H := by
    have hm' := H.mul_mem (H.inv_mem (hRoot 1)) hS
    simpa only [←mul_assoc,inv_mul_cancel,one_mul] using hm'
  exact CFSGTypeAMonomialCycleGeneration.eq_top_of_full_edge (by omega) σ hσ
    W d hW hd H hHW i hi hRoot

end SymmetricSubgroupAsymptotics.CFSGTypeATwistedCycleGeneration
