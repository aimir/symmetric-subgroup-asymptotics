import SymmetricSubgroupAsymptotics.CFSGHermitianCrossDuality
import SymmetricSubgroupAsymptotics.CFSGSesquilinearKernelRigidity

/-! Cross-zero preservation by actual linear pieces has ONE nonzero
cross-pairing multiplier. This retains the scalar discarded by the field
coherence statement and supplies the opposed-range extension algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianCrossPairMultiplier
open CFSGTwistedAUnitaryParameters CFSGHermitianCrossDuality
variable {K I J : Type*} [Field K] [Finite K] [Fintype I] [DecidableEq I] [Fintype J]

theorem exists_cross_pair_multiplier (sigma : K ≃+* K) (H : Matrix J J K)
    (a b a' b' : (I → K) →ₗ[K] (J → K))
    (hND : ∀ v : I → K, (∀ w : I → K, hermitianPair sigma H (a v) (b w) = 0) → v = 0)
    (hzero : ∀ v w, hermitianPair sigma H (a' v) (b' w) = 0 ↔ hermitianPair sigma H (a v) (b w) = 0)
    (i₀ i₁ : I) (hne : i₀ ≠ i₁) :
    ∃ c : K, c ≠ 0 ∧ ∀ v w,
      hermitianPair sigma H (a' v) (b' w) = c * hermitianPair sigma H (a v) (b w) := by
  have hND' (v : I → K) (hv : ∀ w, hermitianPair sigma H (a' v) (b' w) = 0) : v = 0 :=
    hND v (fun w => (hzero v w).mp (hv w))
  let D := crossDuality sigma H a b hND
  let E := crossDuality sigma H a' b' hND'
  obtain ⟨c,hc,he,_⟩ := CFSGSesquilinearKernelRigidity.common_scalar_and_field sigma sigma D E.toAddMonoidHom
    (crossDuality_smul sigma H a b hND) (crossDuality_smul sigma H a' b' hND') hzero i₀ i₁ hne
  refine ⟨c,hc,?_⟩
  intro v w
  have hh := congrArg (fun L : Module.Dual K (I → K) => L w) (he v)
  change hermitianPair sigma H (a' v) (b' w) = c * hermitianPair sigma H (a v) (b w) at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGHermitianCrossPairMultiplier
