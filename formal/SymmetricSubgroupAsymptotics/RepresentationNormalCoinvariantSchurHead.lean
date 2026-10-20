import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre

/-!
# Simple-target Hom bounds from a normal-subgroup head

When a normal subgroup fixes the actual simple target, every intertwiner
descends through the source's coinvariants for that subgroup. The simple
target has Schur capacity at most one, so its Hom dimension is bounded by
the original restricted head. Postcomposition by its division ring makes
that dimension divisible by the target's Schur endomorphism dimension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {k G V W : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (rho : Representation k G V) (sigma : Representation k G W)
  (P : Subgroup G) [P.Normal]
  (hfix : ∀ (g : P) (w : W), sigma g w = w)

/-- The target is fixed by the normal subgroup, so the actual source
intertwiner factors uniquely through its intrinsic coinvariants. -/
def intertwiningNormalCoinvariantsEquiv :
    rho.IntertwiningMap sigma ≃ₗ[k]
      (Representation.toCoinvariants rho P).IntertwiningMap sigma where
  toFun f :=
    { toLinearMap := Representation.Coinvariants.lift (rho.comp P.subtype)
        f.toLinearMap (by
          intro g
          apply LinearMap.ext
          intro v
          exact (Representation.IntertwiningMap.isIntertwining rho sigma f
            (g : G) v).trans (hfix g (f v)))
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro q
        obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
          (rho.comp P.subtype) q
        exact Representation.IntertwiningMap.isIntertwining rho sigma f g v }
  invFun f := f.comp (Representation.toCoinvariantsMkQ rho P)
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rfl
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
      (rho.comp P.subtype) q
    rfl
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
      (rho.comp P.subtype) q
    rfl
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
      (rho.comp P.subtype) q
    rfl

include hfix in
/-- A simple target costs at most the intrinsic normal-subgroup head of
the original source, rather than its ambient dimension. -/
theorem intertwining_finrank_le_normal_coinvariant_head
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule k[G] sigma.asModule] :
    Module.finrank k (rho.IntertwiningMap sigma) ≤
      Module.finrank k
        (Representation.IntertwiningMap (rho.comp P.subtype)
          (Representation.trivial k P k)) := by
  rw [(intertwiningNormalCoinvariantsEquiv rho sigma P hfix).finrank_eq,
    representationHead_finrank_eq_coinvariants]
  have hc : representationSchurCapacity sigma ≤ 1 :=
    schurCapacity_le_one_of_simple (k := k) (R := k[G]) (A := sigma.asModule)
  have hh := intertwiningMap_finrank_le_schur
    (Representation.toCoinvariants rho P) sigma
  have hle : (Module.finrank k
      ((Representation.toCoinvariants rho P).IntertwiningMap sigma) : ℝ) ≤
      Module.finrank k (Representation.Coinvariants (rho.comp P.subtype)) := by
    calc
      _ ≤ representationSchurCapacity sigma *
          Module.finrank k (Representation.Coinvariants (rho.comp P.subtype)) := hh
      _ ≤ 1 * Module.finrank k (Representation.Coinvariants (rho.comp P.subtype)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := one_mul _
  exact_mod_cast hle

omit P [P.Normal] hfix in
/-- The target division ring acts by postcomposition. Its dimension
therefore divides the dimension of every actual intertwiner space. -/
theorem target_end_finrank_dvd_intertwining_finrank
    [IsSimpleModule k[G] sigma.asModule] :
    Module.finrank k (Module.End k[G] sigma.asModule) ∣
      Module.finrank k (rho.IntertwiningMap sigma) := by
  rw [(Representation.IntertwiningMap.equivLinearMapAsModule rho sigma).finrank_eq]
  exact ⟨Module.finrank (Module.End k[G] sigma.asModule)
    (rho.asModule →ₗ[k[G]] sigma.asModule),
    (Module.finrank_mul_finrank k (Module.End k[G] sigma.asModule)
      (rho.asModule →ₗ[k[G]] sigma.asModule)).symm⟩

include hfix in
/-- In the two-dimensional Schur-ring case, an odd upper head bound
rounds down to the preceding even dimension. -/
theorem intertwining_finrank_le_even_of_normal_coinvariant_head
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule k[G] sigma.asModule]
    (hEnd : Module.finrank k (Module.End k[G] sigma.asModule) = 2)
    (n : ℕ)
    (hhead : Module.finrank k
      (Representation.IntertwiningMap (rho.comp P.subtype)
        (Representation.trivial k P k)) ≤ 2 * n + 1) :
    Module.finrank k (rho.IntertwiningMap sigma) ≤ 2 * n := by
  have hle := intertwining_finrank_le_normal_coinvariant_head rho sigma P hfix
  have hdiv := target_end_finrank_dvd_intertwining_finrank rho sigma
  rw [hEnd] at hdiv
  obtain ⟨m, hm⟩ := hdiv
  omega

end SymmetricSubgroupAsymptotics

end
