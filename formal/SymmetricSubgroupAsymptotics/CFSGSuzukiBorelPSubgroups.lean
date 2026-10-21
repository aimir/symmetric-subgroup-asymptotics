import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentProduct
import Mathlib.Algebra.CharP.Reduced

/-! Every actual binary subgroup of the literal Suzuki Borel envelope
lies in its original unipotent subgroup. Only exact U-times-normalized-T
coordinates and the first original matrix row are used; no whole-group
order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiBorelPSubgroups
open Matrix CFSGSuzukiUnipotent

theorem row_pivot_pow {R : Type*} [Semiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n)
    (hrow : ∀ j : Fin n,j≠i → A i j=0) (k : ℕ) :
    (A^k) i i=(A i i)^k := by
  induction k with
  | zero => simp only [pow_zero,Matrix.one_apply_eq]
  | succ k ih =>
    calc
      (A^(k+1)) i i=A i i*(A^k) i i := by
        rw [pow_succ',Matrix.mul_apply]
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [hrow j hji,zero_mul]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      _ = (A i i)^(k+1) := by rw [ih,pow_succ']

theorem unipotent_torus_entry00 (m : ℕ)
    (a b : CFSGSuzukiFieldParameters.Field m)
    (c : (CFSGSuzukiFieldParameters.Field m)ˣ) :
    ((unipotentElement m a b*CFSGSuzukiTorus.normalizedTorusElement m c : Ambient m) :
      CFSG.Models.SuzukiConstruction.Mat m) 0 0=(c : CFSGSuzukiFieldParameters.Field m) := by
  rw [Matrix.GeneralLinearGroup.coe_mul,unipotentElement_coe,
    CFSGSuzukiTorus.normalizedTorusElement_coe]
  simp [CFSGSuzukiTorus.diagonalTorus,Matrix.mul_diagonal,
    CFSG.Models.SuzukiConstruction.unipotent]

theorem borel_first_row (m : ℕ) (g : Ambient m) (hg : g∈borelEnvelope m)
    (j : Fin 4) (hj : j≠0) : (g : CFSG.Models.SuzukiConstruction.Mat m) 0 j=0 := by
  obtain ⟨a,b,c,rfl⟩ := borelEnvelope_factor m g hg
  rw [Matrix.GeneralLinearGroup.coe_mul,unipotentElement_coe,
    CFSGSuzukiTorus.normalizedTorusElement_coe]
  simp only [CFSGSuzukiTorus.diagonalTorus,Matrix.mul_diagonal]
  fin_cases j <;> simp_all [CFSG.Models.SuzukiConstruction.unipotent]

theorem binary_subgroup_le_unipotent (m : ℕ) (P : Subgroup (Ambient m))
    (hP : IsPGroup 2 P) (hPB : P≤borelEnvelope m) : P≤unipotentSubgroup m := by
  intro g hg
  have hrow := borel_first_row m g (hPB hg)
  obtain ⟨k,hk⟩ := hP ⟨g,hg⟩
  have hp : (g : CFSG.Models.SuzukiConstruction.Mat m)^(2^k)=1 :=
    congrArg (fun x : P => (x.val : CFSG.Models.SuzukiConstruction.Mat m)) hk
  have he := congrArg (fun A : CFSG.Models.SuzukiConstruction.Mat m => A 0 0) hp
  dsimp only at he
  rw [row_pivot_pow _ 0 hrow,Matrix.one_apply_eq] at he
  have hg00 : (g : CFSG.Models.SuzukiConstruction.Mat m) 0 0=1 := by
    apply iterateFrobenius_inj (CFSGSuzukiFieldParameters.Field m) 2 k
    simpa only [iterateFrobenius_def,one_pow] using he
  obtain ⟨a,b,c,hfact⟩ := borelEnvelope_factor m g (hPB hg)
  have hc : (c : CFSGSuzukiFieldParameters.Field m)=1 := by
    have hv := congrArg (fun x : Ambient m =>
      (x : CFSG.Models.SuzukiConstruction.Mat m) 0 0) hfact
    dsimp only at hv
    rw [unipotent_torus_entry00] at hv
    exact hv.symm.trans hg00
  have hc1 : c=1 := Units.ext hc
  rw [hfact,hc1,normalizedTorus_one,mul_one]
  exact ⟨a,b,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGSuzukiBorelPSubgroups
