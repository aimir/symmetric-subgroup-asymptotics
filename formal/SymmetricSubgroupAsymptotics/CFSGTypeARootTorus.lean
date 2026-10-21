import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareSpan

/-! Actual diagonal-torus extraction of one full type-A root group.
All elements are literal determinant-one matrices; parameters and
coordinate indices are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootTorus
open Matrix CFSGTypeAElementaryMatrices
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

def torus {i j : n} (hij : i≠j) (g : Fˣ) : SL (n:=n) (F:=F) :=
  elementary hij ((g : F)-1)*elementary (Ne.symm hij) 1*
    elementary hij ((g : F)⁻¹-1)*elementary (Ne.symm hij) (-(g : F))

theorem torus_coe {i j : n} (hij : i≠j) (g : Fˣ) :
    (torus hij g).val=Matrix.diagonal
      (fun k => if k=i then (g : F) else if k=j then (g : F)⁻¹ else 1) := by
  exact diagonal_pair hij (g : F) (Units.ne_zero g)

theorem torus_inv {i j : n} (hij : i≠j) (g : Fˣ) :
    (torus hij g)⁻¹=torus hij g⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (torus hij g).val*(torus hij g⁻¹).val=1
  rw [torus_coe,torus_coe,Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one']
  congr 1
  funext k
  by_cases hki : k=i <;> by_cases hkj : k=j <;>
    simp_all [Units.val_inv_eq_inv_val,Units.ne_zero g]

/-- The literal determinant-one torus scales its root parameter by the
square of the original unit. -/
theorem torus_conjugation {i j : n} (hij : i≠j) (g : Fˣ) (a : F) :
    torus hij g*elementary hij a*(torus hij g)⁻¹=elementary hij ((g : F)^2*a) := by
  rw [torus_inv]
  apply Subtype.ext
  change (torus hij g).val*Matrix.transvection i j a*(torus hij g⁻¹).val=
    Matrix.transvection i j ((g : F)^2*a)
  rw [torus_coe,torus_coe]
  ext r s
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hri : r=i <;> by_cases hrj : r=j <;>
    by_cases hsi : s=i <;> by_cases hsj : s=j <;>
    simp_all [Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
      Units.val_inv_eq_inv_val,Ne.symm hij] <;>
    (try split_ifs) <;> (try simp_all) <;> field_simp [Units.ne_zero g]

/-- Parameters present at one fixed actual root form an additive subgroup. -/
def rootAddParameters (H : Subgroup (SL (n:=n) (F:=F))) {i j : n} (hij : i≠j) : AddSubgroup F where
  carrier := {a | elementary hij a∈H}
  zero_mem' := by
    change elementary hij 0∈H
    rw [elementary_zero]
    exact H.one_mem
  add_mem' := by
    intro a b ha hb
    change elementary hij (a+b)∈H
    rw [elementary_add]
    exact H.mul_mem ha hb
  neg_mem' := by
    intro a ha
    change elementary hij (-a)∈H
    rw [←elementary_inv]
    exact H.inv_mem ha

/-- One nonzero root element and its actual primitive diagonal torus
supply all parameters at that root. -/
theorem all_parameters_of_torus [Finite F]
    (H : Subgroup (SL (n:=n) (F:=F))) {i j : n} (hij : i≠j)
    (g : Fˣ) (hg : ∀ u : Fˣ,u∈Subgroup.zpowers g)
    (hT : torus hij g∈H) (m : F) (hm : m≠0) (hM : elementary hij m∈H) :
    ∀ a : F,elementary hij a∈H := by
  let B := rootAddParameters H hij
  have hscale : ∀ a : F,a∈B→(g : F)^2*a∈B := by
    intro a ha
    change elementary hij ((g : F)^2*a)∈H
    rw [←torus_conjugation]
    exact H.mul_mem (H.mul_mem hT ha) (H.inv_mem hT)
  have hpow : ∀ k : ℕ,m*(g : F)^(2*k)∈B := by
    intro k
    induction k with
    | zero => simpa only [Nat.mul_zero,pow_zero,mul_one] using hM
    | succ k ih =>
      have he : m*(g : F)^(2*(k+1))=(g : F)^2*(m*(g : F)^(2*k)) := by
        rw [Nat.mul_add,pow_add]
        ring
      rw [he]
      exact hscale _ ih
  have he := CFSGFiniteFieldSquareSpan.eq_top_of_scaled_even_powers B g hg m hm hpow
  intro a
  have ha : a∈B := by rw [he];trivial
  exact ha

end SymmetricSubgroupAsymptotics.CFSGTypeARootTorus
