import SymmetricSubgroupAsymptotics.PrimitiveAffineFixedFrameRelativeHead
import SymmetricSubgroupAsymptotics.RepresentationSectionSubrepresentationHead
import Mathlib.RepresentationTheory.Coinduced

/-!
Coinduction from the actual inverse image of a quotient subgroup is the
inflation of coinduction on that quotient. The equivalence is pullback of
functions along the given surjection. Uniform subrepresentation head bounds
therefore transfer without a split extension or an enlarged acting group.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CoinducedQuotientPullback

variable {k G Q V : Type} [Field k] [Group G] [Group Q]
  [AddCommGroup V] [Module k V]
  (pi : G →* Q) (H : Subgroup Q) (rho : Representation k H V)

/-- Restriction of the original quotient map to the exact inverse image. -/
def localMap : H.comap pi →* H where
  toFun g := ⟨pi g.1, g.2⟩
  map_one' := Subtype.ext pi.map_one
  map_mul' g h := Subtype.ext (pi.map_mul g.1 h.1)

abbrev sourceRepresentation : Representation k G
    (Representation.coindV (H.comap pi).subtype
      (rho.comp (localMap pi H))) :=
  Representation.coind (H.comap pi).subtype (rho.comp (localMap pi H))

/-- Pullback uses the same quotient map at every original group element. -/
def pullback : Representation.IntertwiningMap
    ((Representation.coind H.subtype rho).comp pi)
    (sourceRepresentation pi H rho) where
  toLinearMap := {
    toFun f := ⟨fun g => f.1 (pi g), by
      intro h g
      change f.1 (pi ((h : G) * g)) = rho (localMap pi H h) (f.1 (pi g))
      rw [map_mul]
      exact f.2 (localMap pi H h) (pi g)⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change f.1 (pi x * pi g) = f.1 (pi (x * g))
    rw [map_mul]

theorem pullback_injective (hpi : Function.Surjective pi) :
    Function.Injective (pullback pi H rho) := by
  intro f g hfg
  apply Subtype.ext
  funext q
  obtain ⟨x, rfl⟩ := hpi q
  exact congrArg
    (fun f : Representation.coindV (H.comap pi).subtype
      (rho.comp (localMap pi H)) => f.1 x) hfg

private theorem value_eq_of_map_eq
    (f : Representation.coindV (H.comap pi).subtype
      (rho.comp (localMap pi H)))
    {x y : G} (hxy : pi x = pi y) : f.1 x = f.1 y := by
  have hd : pi (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  let d : H.comap pi := ⟨x * y⁻¹, by
    change pi (x * y⁻¹) ∈ H
    rw [hd]
    exact H.one_mem⟩
  have hd1 : localMap pi H d = 1 := Subtype.ext hd
  have hf := f.2 d y
  change f.1 ((x * y⁻¹) * y) = rho (localMap pi H d) (f.1 y) at hf
  simpa only [inv_mul_cancel_right, hd1, map_one, Module.End.one_apply] using hf

theorem pullback_surjective (hpi : Function.Surjective pi) :
    Function.Surjective (pullback pi H rho) := by
  intro f
  let s : Q → G := Function.surjInv hpi
  have hs : Function.RightInverse s pi := Function.rightInverse_surjInv hpi
  let v : Representation.coindV H.subtype rho := ⟨fun q => f.1 (s q), by
    intro h q
    let l : H.comap pi := ⟨s h.1, by
      change pi (s h.1) ∈ H
      rw [hs]
      exact h.2⟩
    have hl : localMap pi H l = h := Subtype.ext (hs h.1)
    have harg : pi (s (h.1 * q)) = pi ((l : G) * s q) := by
      rw [map_mul]
      change pi (s (h.1 * q)) = pi (s h.1) * pi (s q)
      rw [hs, hs, hs]
    change f.1 (s (h.1 * q)) = rho h (f.1 (s q))
    rw [value_eq_of_map_eq pi H rho f harg]
    have hf := f.2 l (s q)
    change f.1 ((l : G) * s q) = rho (localMap pi H l) (f.1 (s q)) at hf
    simpa only [hl] using hf⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  funext g
  change f.1 (s (pi g)) = f.1 g
  exact value_eq_of_map_eq pi H rho f (hs (pi g))

/-- Exact equivalence of the original coinduced representation with an
inflation, rather than an upper bound inherited from an overgroup. -/
def equiv (hpi : Function.Surjective pi) :
    Representation.Equiv ((Representation.coind H.subtype rho).comp pi)
      (sourceRepresentation pi H rho) :=
  (pullback pi H rho).ofBijective
    ⟨pullback_injective pi H rho hpi, pullback_surjective pi H rho hpi⟩

omit H rho in
/-- Every invariant subspace is unchanged by surjective inflation, as is
its head. This statement keeps the scalar field and vectors unchanged. -/
theorem uniform_head_comp_surjective
    (hpi : Function.Surjective pi) (tau : Representation k Q V) (cap : ℕ)
    (hcap : ∀ A : Subrepresentation tau,
      Module.finrank k
        (A.toRepresentation.IntertwiningMap (Representation.trivial k Q k)) ≤ cap)
    (B : Subrepresentation (tau.comp pi)) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤ cap := by
  let A : Subrepresentation tau := {
    toSubmodule := B.toSubmodule
    apply_mem_toSubmodule q v hv := by
      obtain ⟨g, rfl⟩ := hpi q
      exact B.apply_mem_toSubmodule g hv }
  have he := representationHeadCompSurjective_finrank_eq pi hpi A.toRepresentation
  change Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) =
    Module.finrank k
      (A.toRepresentation.IntertwiningMap (Representation.trivial k Q k)) at he
  exact he.trans_le (hcap A)

/-- A checked uniform head bound on a quotient frame applies to the exact
pair-stabilizer-induced frame on the original group. -/
theorem uniform_head_le
    [Finite G] [Finite Q] [FiniteDimensional k V]
    (hpi : Function.Surjective pi) (cap : ℕ)
    (hcap : ∀ A : Subrepresentation (Representation.coind H.subtype rho),
      Module.finrank k
        (A.toRepresentation.IntertwiningMap (Representation.trivial k Q k)) ≤ cap)
    (B : Subrepresentation (sourceRepresentation pi H rho)) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤ cap := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype Q := Fintype.ofFinite Q
  letI : FiniteDimensional k (Representation.coindV H.subtype rho) :=
    FiniteDimensional.of_injective (Representation.coindV H.subtype rho).subtype
      (Representation.coindV H.subtype rho).subtype_injective
  letI : FiniteDimensional k
      (Representation.coindV (H.comap pi).subtype (rho.comp (localMap pi H))) :=
    FiniteDimensional.of_injective
      (Representation.coindV (H.comap pi).subtype (rho.comp (localMap pi H))).subtype
      (Representation.coindV (H.comap pi).subtype
        (rho.comp (localMap pi H))).subtype_injective
  exact uniformSubrepresentationHeadBound_of_injective
    (sourceRepresentation pi H rho) ((Representation.coind H.subtype rho).comp pi)
    (equiv pi H rho hpi).symm.toIntertwiningMap
    (equiv pi H rho hpi).symm.injective cap
    (uniform_head_comp_surjective pi hpi (Representation.coind H.subtype rho) cap hcap) B

end SymmetricSubgroupAsymptotics.CoinducedQuotientPullback

end
