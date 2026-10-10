import SymmetricSubgroupAsymptotics.DiagonalRepeatedIsotypeModuleDimensions

/-!
# Transport between repeated diagonal isotypes

An ambient monomial operator which permutes two character fibres carries
the corresponding encoded pieces of a stable submodule isomorphically.
Only preservation of coordinate zeroes is used; the nonzero local scalar
factors never have to be chosen.

The final comparison identifies the module-valued encoded piece with the
scalar encoded piece from `DiagonalInvariantSubmodules`.  This lets the
literal affine coordinate transport discharge the equidimensionality
premise of the two-or-four rank split.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DiagonalInvariantSubmodules

open DiagonalIsotypeProjection

variable {k ι J V : Type*} [Field k] [Fintype ι]
  [AddCommGroup V] [Module k V]

/-- Restriction to one repeated character fibre, retaining the original
module-valued coordinates. -/
def moduleRestriction (scalar : ι → J → k) (a : Label scalar) :
    (ι → V) →ₗ[k] (Coordinate scalar a → V) where
  toFun v i := v i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extension by zero from one repeated character fibre. -/
def moduleExtension (scalar : ι → J → k) (a : Label scalar) :
    (Coordinate scalar a → V) →ₗ[k] (ι → V) where
  toFun w i := if hi : scalar i = a.1 then w ⟨i, hi⟩ else 0
  map_add' w z := by
    funext i
    by_cases hi : scalar i = a.1 <;> simp [hi]
  map_smul' c w := by
    funext i
    by_cases hi : scalar i = a.1 <;> simp [hi]

@[simp] theorem moduleRestriction_extension
    (scalar : ι → J → k) (a : Label scalar)
    (w : Coordinate scalar a → V) :
    moduleRestriction scalar a (moduleExtension scalar a w) = w := by
  funext i
  simp [moduleRestriction, moduleExtension, i.2]

theorem moduleExtension_restriction_eq_of_supported
    (scalar : ι → J → k) (a : Label scalar) (v : ι → V)
    (hsupport : ∀ i, scalar i ≠ a.1 → v i = 0) :
    moduleExtension scalar a (moduleRestriction scalar a v) = v := by
  funext i
  by_cases hi : scalar i = a.1
  · simp [moduleRestriction, moduleExtension, hi]
  · simp [moduleExtension, hi, hsupport i hi]

/-- The part of an actual module-valued submodule supported on one literal
character fibre. -/
def ModuleEncode
    (scalar : ι → J → k)
    (K : Submodule k (ι → V))
    (a : Label scalar) : Submodule k (Coordinate scalar a → V) :=
  K.comap (moduleExtension scalar a)

/-- The evident inclusion of one encoded component into the original
submodule. -/
def moduleEncodeInclusion
    (scalar : ι → J → k)
    (K : Submodule k (ι → V))
    (a : Label scalar) :
    ModuleEncode scalar K a →ₗ[k] K where
  toFun w := ⟨moduleExtension scalar a w.1, w.2⟩
  map_add' _ _ := Subtype.ext (map_add (moduleExtension scalar a) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (moduleExtension scalar a) _ _)

/-- Restrict an encoded component after an automorphism of the original
submodule.  The hypotheses say that the automorphism carries the `a`
coordinate fibre to the `b` coordinate fibre. -/
def moduleEncodeTransport
    (scalar : ι → J → k)
    (K : Submodule k (ι → V))
    (a b : Label scalar)
    (sigma : Equiv.Perm ι)
    (T : K ≃ₗ[k] K)
    (hlabel : ∀ i, scalar (sigma i) = b.1 ↔ scalar i = a.1)
    (hzero : ∀ (x : K) (i : ι),
      (T x).1 (sigma i) = 0 ↔ x.1 i = 0) :
    ModuleEncode scalar K a →ₗ[k] ModuleEncode scalar K b where
  toFun w := by
    let x : K := moduleEncodeInclusion scalar K a w
    let y : K := T x
    refine ⟨moduleRestriction scalar b y.1, ?_⟩
    change moduleExtension scalar b (moduleRestriction scalar b y.1) ∈ K
    have hySupport : ∀ j, scalar j ≠ b.1 → y.1 j = 0 := by
      intro j hj
      let i := sigma.symm j
      have hia : scalar i ≠ a.1 := by
        intro hi
        apply hj
        have := (hlabel i).2 hi
        simpa only [i, sigma.apply_symm_apply] using this
      have hxi : x.1 i = 0 := by
        simp only [x, moduleEncodeInclusion, moduleExtension]
        exact dif_neg hia
      have hyi : y.1 (sigma i) = 0 := (hzero x i).2 hxi
      simpa only [i, sigma.apply_symm_apply] using hyi
    rw [moduleExtension_restriction_eq_of_supported scalar b y.1 hySupport]
    exact y.2
  map_add' w z := by
    apply Subtype.ext
    funext i
    change (T (moduleEncodeInclusion scalar K a (w + z))).1 i =
      (T (moduleEncodeInclusion scalar K a w)).1 i +
        (T (moduleEncodeInclusion scalar K a z)).1 i
    rw [map_add]
    rfl
  map_smul' c w := by
    apply Subtype.ext
    funext i
    change (T (moduleEncodeInclusion scalar K a (c • w))).1 i =
      c • (T (moduleEncodeInclusion scalar K a w)).1 i
    rw [map_smul]
    rfl

theorem moduleEncodeTransport_injective
    (scalar : ι → J → k)
    (K : Submodule k (ι → V))
    (a b : Label scalar)
    (sigma : Equiv.Perm ι)
    (T : K ≃ₗ[k] K)
    (hlabel : ∀ i, scalar (sigma i) = b.1 ↔ scalar i = a.1)
    (hzero : ∀ (x : K) (i : ι),
      (T x).1 (sigma i) = 0 ↔ x.1 i = 0) :
    Function.Injective
      (moduleEncodeTransport scalar K a b sigma T hlabel hzero) := by
  intro w z hwz
  let x : K := moduleEncodeInclusion scalar K a w
  let x' : K := moduleEncodeInclusion scalar K a z
  have hsupported : ∀ (u : ModuleEncode scalar K a) (j : ι),
      scalar j ≠ b.1 →
        (T (moduleEncodeInclusion scalar K a u)).1 j = 0 := by
    intro u j hj
    let i := sigma.symm j
    have hia : scalar i ≠ a.1 := by
      intro hi
      apply hj
      have := (hlabel i).2 hi
      simpa only [i, sigma.apply_symm_apply] using this
    have hui : (moduleEncodeInclusion scalar K a u).1 i = 0 := by
      simp only [moduleEncodeInclusion, moduleExtension]
      exact dif_neg hia
    have hTi := (hzero (moduleEncodeInclusion scalar K a u) i).2 hui
    simpa only [i, sigma.apply_symm_apply] using hTi
  have hTx : T x = T x' := by
    apply Subtype.ext
    funext j
    by_cases hj : scalar j = b.1
    · let q : Coordinate scalar b := ⟨j, hj⟩
      have hq := congrArg
        (fun u : ModuleEncode scalar K b ↦ u.1 q) hwz
      exact hq
    · rw [hsupported w j hj, hsupported z j hj]
  have hxx : x = x' := T.injective hTx
  apply Subtype.ext
  have hext := congrArg
    (fun u : K ↦ moduleRestriction scalar a u.1) hxx
  simpa only [x, x', moduleEncodeInclusion,
    moduleRestriction_extension] using hext

/-- A monomial coordinate automorphism which exchanges two fibres makes
their module-valued encoded pieces equidimensional. -/
theorem moduleEncode_finrank_eq_of_coordinate_transport
    (scalar : ι → J → k)
    (K : Submodule k (ι → V))
    (a b : Label scalar)
    (sigma : Equiv.Perm ι)
    (T : K ≃ₗ[k] K)
    (hlabel : ∀ i, scalar (sigma i) = b.1 ↔ scalar i = a.1)
    (hzero : ∀ (x : K) (i : ι),
      (T x).1 (sigma i) = 0 ↔ x.1 i = 0) :
    Module.finrank k (ModuleEncode scalar K a) =
      Module.finrank k (ModuleEncode scalar K b) := by
  have hab : Module.finrank k (ModuleEncode scalar K a) ≤
      Module.finrank k (ModuleEncode scalar K b) :=
    (moduleEncodeTransport scalar K a b sigma T hlabel hzero).finrank_le_finrank_of_injective
      (moduleEncodeTransport_injective scalar K a b sigma T hlabel hzero)
  have hlabel' : ∀ j,
      scalar (sigma.symm j) = a.1 ↔ scalar j = b.1 := by
    intro j
    simpa only [sigma.apply_symm_apply] using (hlabel (sigma.symm j)).symm
  have hzero' : ∀ (y : K) (j : ι),
      (T.symm y).1 (sigma.symm j) = 0 ↔ y.1 j = 0 := by
    intro y j
    have h := hzero (T.symm y) (sigma.symm j)
    simpa only [T.apply_symm_apply, sigma.apply_symm_apply] using h.symm
  have hba : Module.finrank k (ModuleEncode scalar K b) ≤
      Module.finrank k (ModuleEncode scalar K a) :=
    (moduleEncodeTransport scalar K b a sigma.symm T.symm hlabel' hzero').finrank_le_finrank_of_injective
      (moduleEncodeTransport_injective scalar K b a sigma.symm T.symm
        hlabel' hzero')
  exact Nat.le_antisymm hab hba

/-- Coordinatewise scalarization on one encoded fibre. -/
def moduleEncodeToScalar
    (scalar : ι → J → k)
    (K : ModuleStable (V := V) scalar)
    (e : V ≃ₗ[k] k)
    (a : Label scalar) :
    ModuleEncode scalar K.1 a →ₗ[k]
      encode scalar (scalarizedStable scalar K e) a where
  toFun w := by
    refine ⟨fun i ↦ e (w.1 i), ?_⟩
    change extension scalar a (fun i ↦ e (w.1 i)) ∈
      K.1.map (pointwiseScalarEquiv (ι := ι) e).toLinearMap
    refine ⟨moduleExtension scalar a w.1, w.2, ?_⟩
    funext i
    by_cases hi : scalar i = a.1 <;>
      simp [pointwiseScalarEquiv, extension, moduleExtension, hi]
  map_add' w z := by
    apply Subtype.ext
    funext i
    exact map_add e (w.1 i) (z.1 i)
  map_smul' c w := by
    apply Subtype.ext
    funext i
    exact map_smul e c (w.1 i)

theorem moduleEncodeToScalar_bijective
    (scalar : ι → J → k)
    (K : ModuleStable (V := V) scalar)
    (e : V ≃ₗ[k] k)
    (a : Label scalar) :
    Function.Bijective (moduleEncodeToScalar scalar K e a) := by
  constructor
  · intro w z h
    apply Subtype.ext
    funext i
    apply e.injective
    exact congrArg
      (fun u : encode scalar (scalarizedStable scalar K e) a ↦ u.1 i) h
  · intro u
    have hu : extension scalar a u.1 ∈
        K.1.map (pointwiseScalarEquiv (ι := ι) e).toLinearMap := u.2
    rcases hu with ⟨x, hx, hxu⟩
    let v : Coordinate scalar a → V := fun i ↦ e.symm (u.1 i)
    have hext : moduleExtension scalar a v = x := by
      apply (pointwiseScalarEquiv (ι := ι) e).injective
      funext i
      have hi := congrFun hxu i
      by_cases hia : scalar i = a.1
      · simpa only [pointwiseScalarEquiv_apply, moduleExtension, dif_pos hia,
          extension, e.apply_symm_apply] using hi.symm
      · simpa only [pointwiseScalarEquiv_apply, moduleExtension, dif_neg hia,
          extension, map_zero] using hi.symm
    let w : ModuleEncode scalar K.1 a := ⟨v, by
      rw [hext]
      exact hx⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    funext i
    exact e.apply_symm_apply (u.1 i)

/-- The module-valued and scalarized encoded pieces have the same
dimension. -/
theorem moduleEncode_finrank_eq_scalarized
    (scalar : ι → J → k)
    (K : ModuleStable (V := V) scalar)
    (e : V ≃ₗ[k] k)
    (a : Label scalar) :
    Module.finrank k (ModuleEncode scalar K.1 a) =
      Module.finrank k (encode scalar (scalarizedStable scalar K e) a) := by
  exact (LinearEquiv.ofBijective (moduleEncodeToScalar scalar K e a)
    (moduleEncodeToScalar_bijective scalar K e a)).finrank_eq

end DiagonalInvariantSubmodules
end SymmetricSubgroupAsymptotics

end
