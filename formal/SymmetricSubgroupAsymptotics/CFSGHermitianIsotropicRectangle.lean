import SymmetricSubgroupAsymptotics.CFSGHermitianPlanePairingValues

/-! A literal isotropic rectangle above two independent opposed
coordinates. Original cross-pairing realizes the dual vectors, and their
mixed cross-value is chosen to cancel the signed Hermitian transpose.
All characteristics, including two, are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem exists_hermitian_isotropic_rectangle
    (eps : K) (heps : eps ≠ 0)
    (hflip : ∀ v w, hermitianPair sigma H v w = eps * sigma (hermitianPair sigma H w v))
    (P Z : IsotropicSpace sigma H) (hdP : Module.finrank K P.val = 2)
    (y : Fin 2 → I → K) (hspan : Submodule.span K (Set.range y) = Z.val)
    (hND : ∀ x ∈ P.val, (∀ z ∈ Z.val, hermitianPair sigma H z x = 0) → x = 0) :
    ∃ x₁ ∈ P.val, ∃ x₂ ∈ P.val, LinearIndependent K ![x₁,x₂] ∧
      hermitianPair sigma H (y 0) x₁ = 0 ∧
      hermitianPair sigma H (y 1) x₂ = 0 ∧
      hermitianPair sigma H (x₁ + y 0) (x₁ + y 0) = 0 ∧
      hermitianPair sigma H (x₂ + y 1) (x₂ + y 1) = 0 ∧
      hermitianPair sigma H (x₁ + y 0) (x₂ + y 1) = 0 := by
  obtain ⟨x₁, hx₁⟩ := planePairingValues_surjective sigma H P.val Z.val hdP y hspan hND ![0,1]
  obtain ⟨x₂, hx₂⟩ := planePairingValues_surjective sigma H P.val Z.val hdP y hspan hND ![-eps,0]
  have h10 := congrFun hx₁ (0 : Fin 2)
  have h11 := congrFun hx₁ (1 : Fin 2)
  have h20 := congrFun hx₂ (0 : Fin 2)
  have h21 := congrFun hx₂ (1 : Fin 2)
  change hermitianPair sigma H (y 0) x₁.val = 0 at h10
  change hermitianPair sigma H (y 1) x₁.val = 1 at h11
  change hermitianPair sigma H (y 0) x₂.val = -eps at h20
  change hermitianPair sigma H (y 1) x₂.val = 0 at h21
  have hli : LinearIndependent K ![x₁.val,x₂.val] := by
    apply LinearIndependent.pair_iff.mpr
    intro c d he
    have h₀ := congrArg (pairRightLinear sigma H (y 0)) he
    rw [map_add, map_smul, map_smul, map_zero] at h₀
    change c * hermitianPair sigma H (y 0) x₁.val +
      d * hermitianPair sigma H (y 0) x₂.val = 0 at h₀
    rw [h10, h20, mul_zero, zero_add] at h₀
    have hd : d = 0 := (mul_eq_zero.mp h₀).resolve_right (neg_ne_zero.mpr heps)
    have h₁ := congrArg (pairRightLinear sigma H (y 1)) he
    rw [map_add, map_smul, map_smul, map_zero] at h₁
    change c * hermitianPair sigma H (y 1) x₁.val +
      d * hermitianPair sigma H (y 1) x₂.val = 0 at h₁
    rw [h11, h21, mul_one, mul_zero, add_zero] at h₁
    exact ⟨h₁, hd⟩
  have hy (j : Fin 2) : y j ∈ Z.val := by
    rw [← hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  have h1flip : hermitianPair sigma H x₁.val (y 0) = 0 := by
    rw [hflip, h10, map_zero, mul_zero]
  have h2flip : hermitianPair sigma H x₂.val (y 1) = 0 := by
    rw [hflip, h21, map_zero, mul_zero]
  have hcross : hermitianPair sigma H x₁.val (y 1) = eps := by
    rw [hflip, h11, map_one, mul_one]
  refine ⟨x₁.val, x₁.property, x₂.val, x₂.property, hli, h10, h21, ?_, ?_, ?_⟩
  · rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
      P.property _ x₁.property _ x₁.property, Z.property _ (hy 0) _ (hy 0), h10, h1flip]
    simp only [zero_add]
  · rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
      P.property _ x₂.property _ x₂.property, Z.property _ (hy 1) _ (hy 1), h21, h2flip]
    simp only [zero_add]
  · rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
      P.property _ x₁.property _ x₂.property, Z.property _ (hy 0) _ (hy 1), hcross, h20]
    simp only [zero_add, add_zero, add_neg_cancel]

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
