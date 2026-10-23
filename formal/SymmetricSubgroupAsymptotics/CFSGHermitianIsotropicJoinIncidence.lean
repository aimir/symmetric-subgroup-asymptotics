import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicSpaceCardinality

/-! Order transport of all isotropic spaces preserves every existing
join. The original point permutation therefore preserves exact
projective line incidence within each singular subspace. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem isotropicOrderIso_map_sup (F : IsotropicSpace sigma H ≃o IsotropicSpace sigma H)
    (S T : IsotropicSpace sigma H)
    (hST : Orthogonal sigma H (S.val ⊔ T.val) (S.val ⊔ T.val)) :
    (F ⟨S.val ⊔ T.val, hST⟩).val = (F S).val ⊔ (F T).val := by
  let J : IsotropicSpace sigma H := ⟨S.val ⊔ T.val, hST⟩
  have hSJ : S ≤ J := by
    change S.val ≤ S.val ⊔ T.val
    exact le_sup_left
  have hTJ : T ≤ J := by
    change T.val ≤ S.val ⊔ T.val
    exact le_sup_right
  have hsup : (F S).val ⊔ (F T).val ≤ (F J).val := sup_le (F.monotone hSJ) (F.monotone hTJ)
  let U : IsotropicSpace sigma H := ⟨(F S).val ⊔ (F T).val,
    fun x hx y hy => (F J).property x (hsup hx) y (hsup hy)⟩
  have hSpre : S ≤ F.symm U := by
    have hh := F.symm.monotone (show F S ≤ U from
      (show (F S).val ≤ (F S).val ⊔ (F T).val from le_sup_left))
    simpa only [OrderIso.symm_apply_apply] using hh
  have hTpre : T ≤ F.symm U := by
    have hh := F.symm.monotone (show F T ≤ U from
      (show (F T).val ≤ (F S).val ⊔ (F T).val from le_sup_right))
    simpa only [OrderIso.symm_apply_apply] using hh
  have hpre : J ≤ F.symm U := by
    change S.val ⊔ T.val ≤ (F.symm U).val
    exact sup_le hSpre hTpre
  have hpost := F.monotone hpre
  have hFU : F J ≤ U := by simpa only [OrderIso.apply_symm_apply] using hpost
  exact (show (F J).val ≤ U.val from hFU).antisymm hsup

variable [Finite K]
variable (hsep : ∀ S : IsotropicSpace sigma H, SeparatedByMaximal sigma H S.val)
variable (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)

include hsep in
theorem isotropicSpaceImage_point (P : SingularPoint sigma H)
    (hP : Orthogonal sigma H P.val P.val) :
    (isotropicSpaceImage sigma H f hf ⟨P.val, hP⟩).val = (f P).val := by
  have hle : (f P).val ≤ (isotropicSpaceImage sigma H f hf ⟨P.val, hP⟩).val :=
    (isotropicSpaceEquiv_incidence sigma H hsep f hf ⟨P.val, hP⟩ P).mpr le_rfl
  have hd := isotropicSpaceImage_finrank sigma H hsep f hf ⟨P.val, hP⟩
  rw [P.property.1] at hd
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hd, (f P).property.1])).symm

include hsep hf in
theorem isotropicSpaceImage_point_join_incidence (S : IsotropicSpace sigma H)
    (P Q R : SingularPoint sigma H) (hP : P.val ≤ S.val) (hQ : Q.val ≤ S.val) :
    (f R).val ≤ (f P).val ⊔ (f Q).val ↔ R.val ≤ P.val ⊔ Q.val := by
  let F := isotropicSpaceOrderIso sigma H hsep f hf
  have hPP : Orthogonal sigma H P.val P.val := fun x hx y hy => S.property x (hP hx) y (hP hy)
  have hQQ : Orthogonal sigma H Q.val Q.val := fun x hx y hy => S.property x (hQ hx) y (hQ hy)
  have hPQ : Orthogonal sigma H (P.val ⊔ Q.val) (P.val ⊔ Q.val) := by
    have hle : P.val ⊔ Q.val ≤ S.val := sup_le hP hQ
    exact fun x hx y hy => S.property x (hle hx) y (hle hy)
  let J : IsotropicSpace sigma H := ⟨P.val ⊔ Q.val, hPQ⟩
  have he : (F J).val = (f P).val ⊔ (f Q).val := by
    have hh := isotropicOrderIso_map_sup sigma H F ⟨P.val, hPP⟩ ⟨Q.val, hQQ⟩ hPQ
    change (F J).val = (isotropicSpaceImage sigma H f hf ⟨P.val, hPP⟩).val ⊔
      (isotropicSpaceImage sigma H f hf ⟨Q.val, hQQ⟩).val at hh
    rw [isotropicSpaceImage_point sigma H hsep f hf, isotropicSpaceImage_point sigma H hsep f hf] at hh
    exact hh
  rw [← he]
  exact isotropicSpaceEquiv_incidence sigma H hsep f hf J R

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
