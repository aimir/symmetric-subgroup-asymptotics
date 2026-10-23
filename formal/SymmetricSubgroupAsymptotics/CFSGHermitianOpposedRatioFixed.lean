import SymmetricSubgroupAsymptotics.CFSGHermitianRectangleRatioFixed
import SymmetricSubgroupAsymptotics.CFSGHermitianPointFunctionals
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! A common ratio on the original orthogonal mixed rays is fixed by
sigma. The actual rectangle and a nonzero cross-value are constructed
from the two opposed planes; no norm or scalar condition is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

private theorem sum_nonzero (P Z : Submodule K (I → K)) (hdis : Disjoint P Z)
    (x y : I → K) (hx : x ∈ P) (hy : y ∈ Z) (hx0 : x ≠ 0) : x + y ≠ 0 := by
  intro h
  have hxZ : x ∈ Z := by
    rw [add_eq_zero_iff_eq_neg.mp h]
    exact Z.neg_mem hy
  exact hx0 ((Submodule.disjoint_def.mp hdis) x hx hxZ)

theorem hermitian_opposed_common_ratio_fixed (sigma : K ≃+* K) (H : Matrix I I K)
    (eps : K) (heps : eps ≠ 0)
    (hflip : ∀ v w, hermitianPair sigma H v w = eps * sigma (hermitianPair sigma H w v))
    (hswap : ∀ v w, hermitianPair sigma H v w = 0 ↔ hermitianPair sigma H w v = 0)
    (P Z : IsotropicSpace sigma H) (hdP : Module.finrank K P.val = 2)
    (hdZ : Module.finrank K Z.val = 2) (hdis : Disjoint P.val Z.val)
    (hNDp : ∀ x ∈ P.val, (∀ y ∈ Z.val, hermitianPair sigma H x y = 0) → x = 0)
    (hNDz : ∀ x ∈ P.val, (∀ y ∈ Z.val, hermitianPair sigma H y x = 0) → x = 0)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (t : K)
    (hratio : ∀ (x y : I → K), x ∈ P.val → x ≠ 0 → y ∈ Z.val → y ≠ 0 →
      hermitianPair sigma H y x = 0 → ∀ (hxy0 : x+y ≠ 0) (hn : hermitianPair sigma H (x+y) (x+y) = 0),
      (f (singularRay sigma H (x+y) hxy0 hn)).val = K ∙ (x+t • y)) : sigma t = t := by
  classical
  let b : Module.Basis (Fin 2) K Z.val := Module.finBasisOfFinrankEq K Z.val hdZ
  let Y : Fin 2 → I → K := fun j => (b j).val
  have hY : LinearIndependent K Y := b.linearIndependent.map' Z.val.subtype Z.val.ker_subtype
  have hYmem (j : Fin 2) : Y j ∈ Z.val := (b j).property
  have hY0 (j : Fin 2) : Y j ≠ 0 := fun h => b.ne_zero j (Subtype.ext h)
  have hle : Submodule.span K (Set.range Y) ≤ Z.val := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hYmem j
  have hdspan : Module.finrank K (Submodule.span K (Set.range Y)) = 2 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hY
  have hspan : Submodule.span K (Set.range Y) = Z.val :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hdZ,hdspan])
  obtain ⟨x,hx,u,hu,hxu,hYx,hYu,hnx,hnu,hpair⟩ :=
    exists_hermitian_isotropic_rectangle sigma H eps heps hflip P Z hdP Y hspan hNDz
  have hx0 : x ≠ 0 := hxu.ne_zero 0
  have hu0 : u ≠ 0 := hxu.ne_zero 1
  have hcross : hermitianPair sigma H x (Y 1) ≠ 0 := by
    intro hz
    have hker : Z.val ≤ (pairRightLinear sigma H x).ker := by
      rw [←hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      fin_cases j
      · change hermitianPair sigma H x (Y 0) = 0
        exact (hswap (Y 0) x).mp hYx
      · change hermitianPair sigma H x (Y 1) = 0
        exact hz
    exact hx0 (hNDp x hx (fun y hy => hker hy))
  have hxsum := sum_nonzero P.val Z.val hdis x (Y 0) hx (hYmem 0) hx0
  have husum := sum_nonzero P.val Z.val hdis u (Y 1) hu (hYmem 1) hu0
  let A := singularRay sigma H (x+Y 0) hxsum hnx
  let B := singularRay sigma H (u+Y 1) husum hnu
  have hAB : Orthogonal sigma H A.val B.val :=
    (orthogonal_iff_singular_representatives sigma H A B _ _
      (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _) hxsum husum).mpr hpair
  have himage := (hf A B).mpr hAB
  have hA : (f A).val = K ∙ (x+t • Y 0) := hratio x (Y 0) hx hx0 (hYmem 0) (hY0 0) hYx hxsum hnx
  have hB : (f B).val = K ∙ (u+t • Y 1) := hratio u (Y 1) hu hu0 (hYmem 1) (hY0 1) hYu husum hnu
  have hAx : x+t • Y 0 ∈ (f A).val := by
    rw [hA]
    exact Submodule.mem_span_singleton_self _
  have hBu : u+t • Y 1 ∈ (f B).val := by
    rw [hB]
    exact Submodule.mem_span_singleton_self _
  exact hermitian_rectangle_mixed_ratio_fixed sigma H x u (Y 0) (Y 1) t
    (P.property x hx u hu) (Z.property _ (hYmem 0) _ (hYmem 1)) hcross hpair
    (himage _ hAx _ hBu)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
