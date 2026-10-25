import SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalBasis
import SymmetricSubgroupAsymptotics.CFSGQuadraticNormFibreCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import SymmetricSubgroupAsymptotics.CFSGHermitianMatrixPullback

/-! Actual quadratic-field structure supplies ALL structural hypotheses
for Gram--Schmidt on a nonzero scalar multiple of the original invertible
matrix. The original matrix is retained for the nondegeneracy proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticHermitianScaledBasis
open Module CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists

theorem exists_basis (q : CFSG.PrimePower)
    {I : Type*} [Fintype I] [DecidableEq I]
    (H : (Matrix I I (q.Extension 2))ˣ) (c : q.Extension 2) (hc : c ≠ 0)
    (hrec : ∀ x y : I → q.Extension 2,
      definingFieldAutomorphism q 2
          (hermitianPair (definingFieldAutomorphism q 2) (c • H.val) x y)=
        hermitianPair (definingFieldAutomorphism q 2) (c • H.val) y x) :
    ∃ b : Basis (Fin (Fintype.card I)) (q.Extension 2) (I → q.Extension 2),
      ∀ i j, hermitianPair (definingFieldAutomorphism q 2) (c • H.val)
        (b i) (b j)=if i=j then 1 else 0 := by
  classical
  let sigma := definingFieldAutomorphism q 2
  let A := c • H.val
  have hswap (x y : I → q.Extension 2) :
      hermitianPair sigma A x y=0 ↔ hermitianPair sigma A y x=0 := by
    constructor
    · intro h
      have hh := hrec x y
      rw [h,map_zero] at hh
      exact hh.symm
    · intro h
      have hh := hrec y x
      rw [h,map_zero] at hh
      exact hh.symm
  have hnorm (a : q.Extension 2) (_ : a ≠ 0) (ha : sigma a=a) :
      ∃ t : q.Extension 2, sigma t*t=a := by
    obtain ⟨t,ht⟩ := CFSGTwistedA2UnipotentArrays.exists_norm_eq_fixed q a ha
    exact ⟨t,(mul_comm _ _).trans ht⟩
  let W : Submodule (q.Extension 2) (I → q.Extension 2) := ⊤
  have hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma A x y=0) → x=0 := by
    intro x _ hz
    by_contra hx
    obtain ⟨y,hy⟩ := hermitianPair_surjective sigma H x hx 1
    have hh := hz y (by trivial)
    change hermitianPair sigma (c • H.val) x y=0 at hh
    rw [CFSGHermitianMatrixPullback.scalar_form,hy,mul_one] at hh
    exact hc hh
  obtain ⟨b,hb⟩ := FiniteHermitianOrthonormalBasis.exists_subspace_basis sigma A
    (CFSGTwistedAQuadraticTrace.exists_nonfixed q) hswap (fun x => hrec x x) hnorm W hND
  have hn : Module.finrank (q.Extension 2) W=Fintype.card I := by
    change Module.finrank (q.Extension 2) (⊤ : Submodule (q.Extension 2) (I → q.Extension 2))=_
    rw [finrank_top,Module.finrank_pi]
  let bA := (b.map (Submodule.topEquiv : W ≃ₗ[q.Extension 2] (I → q.Extension 2))).reindex
    (finCongr hn)
  refine ⟨bA,?_⟩
  intro i j
  change hermitianPair sigma A
    (((b.map Submodule.topEquiv).reindex (finCongr hn)) i)
    (((b.map Submodule.topEquiv).reindex (finCongr hn)) j)=_
  rw [Basis.reindex_apply,Basis.reindex_apply,Basis.map_apply,Basis.map_apply]
  change hermitianPair sigma A
    (b ((finCongr hn).symm i)).val (b ((finCongr hn).symm j)).val=if i=j then 1 else 0
  simpa only [Equiv.apply_eq_iff_eq] using hb ((finCongr hn).symm i) ((finCongr hn).symm j)

end SymmetricSubgroupAsymptotics.CFSGQuadraticHermitianScaledBasis
