import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentSylow
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveCenter

/-! The central quotient is injective on the SAME literal unipotent
group: a scalar unitriangular matrix is the identity. Consequently
the original and projective defining-characteristic Sylows are
actually isomorphic, in every characteristic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices

def unipotentProjectiveHom (K : Type) [Field K] (r : ℕ) :
    unipotent K (r + 1) →* elementaryProjective K (r + 1) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))).comp
    (unipotent K (r + 1)).subtype

theorem unipotentProjectiveHom_injective (K : Type) [Field K] (r : ℕ) :
    Function.Injective (unipotentProjectiveHom K r) := by
  apply (injective_iff_map_eq_one _).mpr
  intro u hu
  have hz : u.val ∈ Subgroup.center (elementaryRootGroup K (r + 1)) :=
    (QuotientGroup.eq_one_iff u.val).mp hu
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r u.val).mp hz
  have hdiag := u.property.2 (Sum.inl (0 : Fin (r + 1)))
  change (u.val.val : Mat K (r + 1))
    (Sum.inl (0 : Fin (r + 1))) (Sum.inl (0 : Fin (r + 1))) = 1 at hdiag
  have hentry := congrArg (fun M : Mat K (r + 1) =>
    M (Sum.inl (0 : Fin (r + 1))) (Sum.inl (0 : Fin (r + 1)))) hc
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hentry
  have hc1 : c = 1 := hentry.symm.trans hdiag
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa only [hc1, one_smul] using hc

def projectiveUnipotent (K : Type) [Field K] (r : ℕ) :
    Subgroup (elementaryProjective K (r + 1)) :=
  (unipotent K (r + 1)).map
    (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1))))

def unipotentProjectiveEquiv (K : Type) [Field K] (r : ℕ) :
    unipotent K (r + 1) ≃* projectiveUnipotent K r :=
  MulEquiv.ofBijective
    ((QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))).subgroupMap
      (unipotent K (r + 1)))
    ⟨fun _ _ he => unipotentProjectiveHom_injective K r (congrArg Subtype.val he),
      MonoidHom.subgroupMap_surjective _ _⟩

@[simp] theorem unipotentProjectiveEquiv_apply (K : Type) [Field K] (r : ℕ)
    (u : unipotent K (r + 1)) :
    (unipotentProjectiveEquiv K r u).val = unipotentProjectiveHom K r u := rfl

def projectiveUnipotentSylow (K : Type) [Field K] [Finite K] (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) :
    Sylow p (elementaryProjective K (r + 1)) :=
  (unipotentSylow K p r hr).mapSurjective
    (f := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1))))
    (QuotientGroup.mk'_surjective _)

@[simp] theorem projectiveUnipotentSylow_coe (K : Type) [Field K] [Finite K] (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) :
    (projectiveUnipotentSylow K p r hr : Subgroup (elementaryProjective K (r + 1))) =
      projectiveUnipotent K r := rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
