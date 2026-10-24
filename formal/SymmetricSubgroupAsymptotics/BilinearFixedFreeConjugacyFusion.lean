import SymmetricSubgroupAsymptotics.FixedFreeInvariantFormCongruence
import SymmetricSubgroupAsymptotics.QuadraticIsometryPolarStabilizer

/-! Fixed-point-free conjugacy in the literal full bilinear-preserver
group agrees with conjugacy in the actual general linear group in
characteristic two. Pullback of the SAME reference form and the
constructed centralizer congruence prove the fusion statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BilinearFixedFreeConjugacyFusion
open QuadraticIsometryPolarStabilizer FixedFreeInvariantFormCongruence

variable {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Finite V] [Nontrivial V]

theorem isConj_of_fixedFree (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hBs : B.IsSymm) (X Y : polarPreservers B)
    (hfixed : ∀ x : V, X.val x=x → x=0) (hconj : IsConj X.val Y.val) : IsConj X Y := by
  obtain ⟨P,hP⟩ := isConj_iff.mp hconj
  have hPX (x:V) : P (X.val x)=Y.val (P x) := by
    have he := LinearEquiv.congr_fun hP (P x)
    change P (X.val (P.symm (P x)))=Y.val (P x) at he
    rw [P.symm_apply_apply] at he
    exact he
  let C : LinearMap.BilinForm K V := B.comp P.toLinearMap P.toLinearMap
  have hC : C.Nondegenerate := by
    constructor
    · intro x hx
      have hp : P x=0 := hB.1 (P x) (fun y => by
        have he := hx (P.symm y)
        change B (P x) (P (P.symm y))=0 at he
        simpa only [P.apply_symm_apply] using he)
      apply P.injective
      simpa only [map_zero] using hp
    · intro y hy
      have hp : P y=0 := hB.2 (P y) (fun x => by
        have he := hy (P.symm x)
        change B (P (P.symm x)) (P y)=0 at he
        simpa only [P.apply_symm_apply] using he)
      apply P.injective
      simpa only [map_zero] using hp
  have hCs : C.IsSymm := ⟨fun x y => hBs.eq (P x) (P y)⟩
  have hCA (x y:V) : C (X.val x) (X.val y)=C x y := by
    change B (P (X.val x)) (P (X.val y))=B (P x) (P y)
    rw [hPX,hPX]
    exact Y.property (P x) (P y)
  obtain ⟨T,hTc,hT⟩ := exists_commuting_congruence B C hB hC hBs hCs X.val
    X.property hCA hfixed
  have hInv (x:V) : T.symm (X.val x)=X.val (T.symm x) := by
    have he := LinearMap.congr_fun hTc.eq (T.symm x)
    change T (X.val (T.symm x))=X.val (T (T.symm x)) at he
    rw [T.apply_symm_apply] at he
    have hh := congrArg T.symm he
    rw [T.symm_apply_apply] at hh
    exact hh.symm
  let G : V ≃ₗ[K] V := P*T⁻¹
  have hG : G∈polarPreservers B := by
    intro x y
    have he := hT (T.symm x) (T.symm y)
    rw [T.apply_symm_apply,T.apply_symm_apply] at he
    exact he.symm
  have hGX (x:V) : G (X.val x)=Y.val (G x) := by
    change P (T.symm (X.val x))=Y.val (P (T.symm x))
    rw [hInv,hPX]
  apply isConj_iff.mpr
  refine ⟨⟨G,hG⟩,?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change G (X.val (G.symm x))=Y.val x
  rw [hGX,G.apply_symm_apply]

theorem isConj_iff_gl_of_fixedFree (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hBs : B.IsSymm) (X Y : polarPreservers B)
    (hfixed : ∀ x : V, X.val x=x → x=0) :
    IsConj X Y ↔ IsConj X.val Y.val := by
  constructor
  · intro h
    obtain ⟨g,hg⟩ := isConj_iff.mp h
    exact isConj_iff.mpr ⟨g.val,congrArg (fun a:polarPreservers B => a.val) hg⟩
  · exact isConj_of_fixedFree B hB hBs X Y hfixed

end SymmetricSubgroupAsymptotics.BilinearFixedFreeConjugacyFusion
