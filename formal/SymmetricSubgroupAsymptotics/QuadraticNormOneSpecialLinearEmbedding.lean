import Mathlib.RingTheory.Norm.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.GroupTheory.Index

/-! The literal multiplication representation of norm-one units in an actual
quadratic algebra. Its projective kernel is retained as the preimage of the
actual SL2 center; no nonsplit-torus conjugacy or normalizer is postulated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuadraticNormOneSpecialLinearEmbedding
variable (F K : Type*) [Field F] [Field K] [Algebra F K]

abbrev normUnits : Kˣ →* Fˣ := Units.map (Algebra.norm F (S:=K))
abbrev NormOne := (normUnits F K).ker

variable {F K}

def slHom (b : Module.Basis (Fin 2) F K) :
    NormOne F K →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun u := ⟨Algebra.leftMulMatrix b (u.val : K),by
    rw [←Algebra.norm_eq_matrix_det b]
    exact congrArg (fun z : Fˣ => (z : F)) u.property⟩
  map_one' := Subtype.ext ((Algebra.leftMulMatrix b).map_one)
  map_mul' u v := Subtype.ext ((Algebra.leftMulMatrix b).map_mul (u.val : K) (v.val : K))

@[simp] theorem slHom_matrix (b : Module.Basis (Fin 2) F K) (u : NormOne F K) :
    (slHom b u).val=Algebra.leftMulMatrix b (u.val : K) := rfl

theorem slHom_injective (b : Module.Basis (Fin 2) F K) : Function.Injective (slHom b) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  exact Algebra.leftMulMatrix_injective b
    (congrArg (fun a : Matrix.SpecialLinearGroup (Fin 2) F => a.val) h)

/-- The target is the original quotient by the actual special-linear center. -/
def projectiveHom (b : Module.Basis (Fin 2) F K) :
    NormOne F K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp (slHom b)

theorem projective_kernel (b : Module.Basis (Fin 2) F K) :
    (projectiveHom b).ker=
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).comap (slHom b) := by
  ext u
  exact QuotientGroup.eq_one_iff _

/-- The SL embedding is genuinely faithful on the norm-one group, before any
central projectivization. -/
theorem card_sl_range [Finite K] (b : Module.Basis (Fin 2) F K) :
    Nat.card (slHom b).range=Nat.card (NormOne F K) :=
  Nat.card_congr (MonoidHom.ofInjective (slHom_injective b)).toEquiv.symm

end SymmetricSubgroupAsymptotics.QuadraticNormOneSpecialLinearEmbedding
