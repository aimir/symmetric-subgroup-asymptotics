import SymmetricSubgroupAsymptotics.CFSGHermitianCodimensionOneExtension

/-! In full rank, the given concrete isometry is already an ambient
equivalence. Injectivity is derived from the original restricted pairing
and surjectivity from equal finite dimensions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianFullRankExtension
open CFSGTwistedAUnitaryParameters CFSGHermitianCodimensionOneExtension
variable {K I : Type*} [Field K] [Fintype I]

theorem exists_extension (sigma : K ≃+* K) (H : Matrix I I K)
    (W : Submodule K (I → K)) (a : W →ₗ[K] (I → K))
    (hW : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0)
    (hpair : ∀ x y : W, hermitianPair sigma H (a x) (a y) = hermitianPair sigma H x.val y.val)
    (hdim : Module.finrank K W = Fintype.card I) :
    ∃ e : (I → K) ≃ₗ[K] (I → K),
      (∀ x y, hermitianPair sigma H (e x) (e y) = hermitianPair sigma H x y) ∧
      ∀ w : W, e w.val = a w := by
  have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa only [Module.finrank_pi] using hdim)
  let S : W ≃ₗ[K] (I → K) := LinearEquiv.ofTop W htop
  let T : W ≃ₗ[K] (I → K) := LinearEquiv.ofInjectiveOfFinrankEq a
    (isometry_injective sigma H W a hW hpair) (by simpa only [Module.finrank_pi] using hdim)
  let e := S.symm.trans T
  refine ⟨e,?_,?_⟩
  · intro x y
    obtain ⟨u,rfl⟩ := S.surjective x
    obtain ⟨v,rfl⟩ := S.surjective y
    change hermitianPair sigma H (T (S.symm (S u))) (T (S.symm (S v))) = _
    rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
    exact hpair u v
  · intro w
    change T (S.symm (S w)) = a w
    rw [LinearEquiv.symm_apply_apply]
    rfl

end SymmetricSubgroupAsymptotics.CFSGHermitianFullRankExtension
