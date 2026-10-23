import SymmetricSubgroupAsymptotics.CFSGQuadraticRootReindex
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl
import Mathlib.Algebra.Group.Units.Equiv

/-! Literal diagram--field twists on any actual integral quadratic root
datum. The full elementary group is preserved because every displayed
root unit is transported to the corresponding root unit, with parameters
acted on by the same field automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramFieldTwist
open CFSGSerreQuadraticMatrix CFSGQuadraticRootReindex
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]

def matrixTwist (e : Equiv.Perm I) (K : Type*) [CommRing K] (sigma : K≃+*K) :
    Matrix I I K≃+*Matrix I I K :=
  sigma.mapMatrix.trans (Matrix.reindexAlgEquiv K K e).toRingEquiv

def unitTwist (e : Equiv.Perm I) (K : Type*) [CommRing K] (sigma : K≃+*K) :
    MulAut ((Matrix I I K)ˣ) := Units.mapEquiv (matrixTwist e K sigma).toMulEquiv

variable (D : Data A I) (p : Equiv.Perm (Fin n)) (e : Equiv.Perm I)
    (hroot : ∀neg i,Matrix.reindexAlgEquiv ℤ ℤ e (integerRoot D neg i)=integerRoot D neg (p i))

include p hroot

theorem unitTwist_root (K : Type*) [CommRing K] (sigma : K≃+*K)
    (neg : Bool) (i : Fin n) (t : K) :
    unitTwist e K sigma (canonicalRoot D K neg i t)=canonicalRoot D K neg (p i) (sigma t) := by
  apply Units.ext
  change Matrix.reindexAlgEquiv K K e
    (sigma.toRingHom.mapMatrix (canonicalRoot D K neg i t : Matrix I I K))=_
  rw [map_canonicalRoot_val,canonicalRoot_val,canonicalRoot_val]
  simp only [map_add,map_one,map_smul,fieldRoot_reindex D e p hroot,
    fieldSecond_reindex D e p hroot]
  rfl

theorem elementary_twist_map (K : Type) [Field K] (sigma : K≃+*K) :
    (canonicalElementaryGroup D K).map (unitTwist e K sigma).toMonoidHom=
      canonicalElementaryGroup D K := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨neg,i,t,rfl⟩
    change unitTwist e K sigma (canonicalRoot D K neg i t)∈canonicalElementaryGroup D K
    rw [unitTwist_root D p e hroot]
    exact Subgroup.subset_closure ⟨neg,p i,sigma t,rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨neg,i,t,rfl⟩
    refine ⟨canonicalRoot D K neg (p.symm i) (sigma.symm t),
      Subgroup.subset_closure ⟨neg,p.symm i,sigma.symm t,rfl⟩,?_⟩
    change unitTwist e K sigma (canonicalRoot D K neg (p.symm i) (sigma.symm t))=_
    rw [unitTwist_root D p e hroot,Equiv.apply_symm_apply,RingEquiv.apply_symm_apply]

def elementaryTwist (K : Type) [Field K] (sigma : K≃+*K) :
    MulAut (canonicalElementaryGroup D K) :=
  ((unitTwist e K sigma).subgroupMap (canonicalElementaryGroup D K)).trans
    (MulEquiv.subgroupCongr (elementary_twist_map D p e hroot K sigma))

theorem elementaryTwist_val (K : Type) [Field K] (sigma : K≃+*K)
    (g : canonicalElementaryGroup D K) :
    (elementaryTwist D p e hroot K sigma g).val=unitTwist e K sigma g.val := rfl

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramFieldTwist
