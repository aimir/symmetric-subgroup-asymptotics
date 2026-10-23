import SymmetricSubgroupAsymptotics.CFSGHermitianCrossPairMultiplier
import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedPieceFields

/-! The actual point-orthogonality action supplies the cross-zero tests
for the constructed local linear pieces. One nonzero multiplier holds
on their whole original opposed spaces, in every dimension at least two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K J : Type*} [Field K] [Finite K] [Fintype J]

theorem linearPiece_opposed_pair_multiplier (sigma : K ≃+* K) (H : Matrix J J K)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (d : ℕ)
    (hP : Module.finrank K P.val = d+2) (hZ : Module.finrank K Z.val = d+2)
    (hND : ∀ x : P.val, (∀ y : Z.val, hermitianPair sigma H x.val y.val = 0) → x = 0)
    (F : SemilinearPiece sigma H f P (RingEquiv.refl K))
    (G : SemilinearPiece sigma H f Z (RingEquiv.refl K)) :
    ∃ c : K, c ≠ 0 ∧ ∀ (x : P.val) (y : Z.val),
      hermitianPair sigma H (F.map x) (G.map y) = c * hermitianPair sigma H x.val y.val := by
  classical
  let eP : (Fin (d+2) → K) ≃ₗ[K] P.val := LinearEquiv.ofFinrankEq _ _ (by simp [hP])
  let eZ : (Fin (d+2) → K) ≃ₗ[K] Z.val := LinearEquiv.ofFinrankEq _ _ (by simp [hZ])
  let a : (Fin (d+2) → K) →ₗ[K] (J → K) := P.val.subtype.comp eP.toLinearMap
  let b : (Fin (d+2) → K) →ₗ[K] (J → K) := Z.val.subtype.comp eZ.toLinearMap
  have hNDc (v : Fin (d+2) → K) (hv : ∀ w, hermitianPair sigma H (a v) (b w) = 0) : v = 0 := by
    have hx : eP v = 0 := by
      apply hND
      intro y
      obtain ⟨w,rfl⟩ := eZ.surjective y
      exact hv w
    exact eP.injective (hx.trans eP.map_zero.symm)
  have h01 : (⟨0,by omega⟩ : Fin (d+2)) ≠ ⟨1,by omega⟩ := by
    intro h
    have he : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  obtain ⟨c,hc,hpair⟩ := CFSGHermitianCrossPairMultiplier.exists_cross_pair_multiplier sigma H a b
    (F.map.comp eP.toLinearMap) (G.map.comp eZ.toLinearMap) hNDc
    (fun v w => semilinearPiece_cross_zero_iff sigma H f hf P Z (RingEquiv.refl K) (RingEquiv.refl K)
      F G (eP v) (eZ w)) ⟨0,by omega⟩ ⟨1,by omega⟩ h01
  refine ⟨c,hc,?_⟩
  intro x y
  obtain ⟨v,rfl⟩ := eP.surjective x
  obtain ⟨w,rfl⟩ := eZ.surjective y
  exact hpair v w

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
