import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRootAdditive

/-! The actual parameter range of one canonical root unit is already
a subgroup. No injectivity or field restriction is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem canonicalRoot_zero (K : Type*) [CommRing K] (neg : Bool) (i : Fin r) :
    canonicalRoot D K neg i 0=1 := by
  apply Units.ext
  simp only [canonicalRoot_val,zero_smul,zero_pow (by decide : 2≠0),add_zero,Units.val_one]

def canonicalRootSubgroup (K : Type*) [CommRing K] (neg : Bool) (i : Fin r) :
    Subgroup (Matrix I I K)ˣ where
  carrier := Set.range (canonicalRoot D K neg i)
  one_mem' := ⟨0,canonicalRoot_zero D K neg i⟩
  mul_mem' := by
    rintro _ _ ⟨t,rfl⟩ ⟨u,rfl⟩
    exact ⟨t+u,(canonicalRoot_add D K neg i t u).symm⟩
  inv_mem' := by
    rintro _ ⟨t,rfl⟩
    exact ⟨-t,(canonicalRoot_inverse D K neg i t).symm⟩

theorem canonicalRoot_mem_subgroup (K : Type*) [CommRing K] (neg : Bool)
    (i : Fin r) (a : K) : canonicalRoot D K neg i a∈canonicalRootSubgroup D K neg i :=
  ⟨a,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
