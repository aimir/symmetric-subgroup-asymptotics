import SymmetricSubgroupAsymptotics.External.CFSG.Models.Suzuki

/-! Canonical invertible lifts of the original Suzuki torus and Weyl
arrays. These are actual members of the original generated model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiTorus
open CFSG.Models.SuzukiConstruction

abbrev Ambient (m : ℕ) := Matrix.GeneralLinearGroup (Fin 4) (CFSG.Models.SuzukiConstruction.Field m)

def torusElement (m : ℕ) (c : (Field m)ˣ) : Ambient m :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (torus m c)
    (by rw [torus_det];exact one_ne_zero)

def weylElement (m : ℕ) : Ambient m :=
  ⟨weyl m,weyl m,weyl_sq m,weyl_sq m⟩

@[simp] theorem torusElement_coe (m : ℕ) (c : (Field m)ˣ) :
    (torusElement m c : Mat m)=torus m c := rfl

@[simp] theorem weylElement_coe (m : ℕ) : (weylElement m : Mat m)=weyl m := rfl

@[simp] theorem torusElement_one (m : ℕ) : torusElement m 1=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torus]

theorem torusElement_mul (m : ℕ) (c d : (Field m)ˣ) :
    torusElement m (c*d)=torusElement m c*torusElement m d := by
  apply Units.ext
  change torus m (c*d)=torus m c*torus m d
  simp only [torus,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_pow,mul_comm]

@[simp] theorem torusElement_inv (m : ℕ) (c : (Field m)ˣ) :
    (torusElement m c)⁻¹=torusElement m c⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [←torusElement_mul,mul_inv_cancel,torusElement_one]

def torusHom (m : ℕ) : (Field m)ˣ→*Ambient m where
  toFun := torusElement m
  map_one' := torusElement_one m
  map_mul' := torusElement_mul m

@[simp] theorem weylElement_square (m : ℕ) : weylElement m*weylElement m=1 := by
  apply Units.ext
  exact weyl_sq m

@[simp] theorem weylElement_inv (m : ℕ) : (weylElement m)⁻¹=weylElement m :=
  inv_eq_of_mul_eq_one_right (weylElement_square m)

theorem torusElement_mem_model (m : ℕ) (c : (Field m)ˣ) : torusElement m c∈subgroup m :=
  Subgroup.subset_closure (Or.inr (Or.inl ⟨c,rfl⟩))

theorem weylElement_mem_model (m : ℕ) : weylElement m∈subgroup m :=
  Subgroup.subset_closure (Or.inr (Or.inr rfl))

end SymmetricSubgroupAsymptotics.CFSGSuzukiTorus
