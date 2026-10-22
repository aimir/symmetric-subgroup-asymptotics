import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceEquivalence

/-! The actual point map restricts to projective line incidence on
every singular subspace. This is proved before any semilinear theorem
is applied to its projective coordinates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem point_le_iff_eq (B : LinearMap.BilinForm K V) (P Q : Points B) : P.val ≤ Q.val ↔ P=Q := by
  constructor
  · intro h
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_le h (by rw [P.property.1,Q.property.1]))
  · rintro rfl
    exact le_rfl

variable (B : LinearMap.BilinForm K V) (f : Points B≃Points B) (l : Planes B≃Planes B)
    (hinc : ∀P L,(f P).val ≤ (l L).val ↔ P.val ≤ L.val)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)

include l hinc horth in
theorem preserves_point_join_incidence (W : Subspaces B) (P Q Z : Points B)
    (hP : P.val ≤ W.val) (hQ : Q.val ≤ W.val) :
    (f Z).val ≤ (f P).val⊔(f Q).val ↔ Z.val ≤ P.val⊔Q.val := by
  by_cases he : P=Q
  · subst Q
    simp only [sup_idem,point_le_iff_eq,f.injective.eq_iff]
  let L := joinPlane B W P Q hP hQ he
  have hfp := (point_le_image_iff B f l hinc W P).mpr hP
  have hfq := (point_le_image_iff B f l hinc W Q).mpr hQ
  let L' := joinPlane B (imageSubspace B f l hinc horth W) (f P) (f Q) hfp hfq
    (fun h=>he (f.injective h))
  have hd : Module.finrank K ((f P).val⊔(f Q).val : Submodule K V)=2 := L'.property.1
  have hle : (f P).val⊔(f Q).val ≤ (l L).val :=
    sup_le ((hinc P L).mpr le_sup_left) ((hinc Q L).mpr le_sup_right)
  have heq : (f P).val⊔(f Q).val=(l L).val := Submodule.eq_of_le_of_finrank_le hle
    (by rw [(l L).property.1,hd])
  rw [heq]
  exact hinc Z L

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
