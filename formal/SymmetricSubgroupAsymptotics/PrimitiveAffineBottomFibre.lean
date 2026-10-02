import SymmetricSubgroupAsymptotics.PrimitiveAffineNormalAxisReduction
import SymmetricSubgroupAsymptotics.FusionEpimorphismLifts
import SymmetricSubgroupAsymptotics.BinaryPairRepresentation
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank
import Mathlib.RingTheory.LittleWedderburn

/-!
# The original bottom fibre of a primitive affine group

The source of every lift is the literal subgroup `J ≤ S_b`.  This file first
removes the rank hypothesis from the general Schur lift theorem: the Sylow
subgroup of every quotient kernel embeds back into that same `J`, so the
permutation prime-rank theorem applies directly.  The remaining construction
identifies the actual translation kernel of a primitive affine group with its
elementary module, retaining the original conjugation action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

/-- The Frattini coordinate rank of the actual Sylow subgroup of a quotient
kernel is bounded inside the original permutation source.  No quotient action,
abstract replacement group, or rank hypothesis is introduced. -/
theorem originalQuotientKernelSylow_primeAbelianization_rank_le
    (p : ℕ) [Fact p.Prime] {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b)))
    {B : Type} [Group B] [Finite B]
    (beta : GroupEpimorphism J B) (P : Sylow p beta.1.ker) :
    Module.finrank (ZMod p)
        (PrimeAbelianization p (P : Subgroup beta.1.ker)) ≤ b / p := by
  let f : (P : Subgroup beta.1.ker) →* J :=
    beta.1.ker.subtype.comp (P : Subgroup beta.1.ker).subtype
  have hf : Function.Injective f :=
    Subtype.val_injective.comp Subtype.val_injective
  let T : Subgroup J := f.range
  let e : (P : Subgroup beta.1.ker) ≃* T :=
    MonoidHom.ofInjective (f := f) hf
  change Module.finrank (ZMod p)
    (Module.Dual (ZMod p) (PrimeCharacters p (P : Subgroup beta.1.ker))) ≤ b / p
  rw [Subspace.dual_finrank_eq, primeCharacter_finrank_congr p e]
  exact primeRank_le_of_subgroup p J T

/-- The Schur lift estimate with the source-rank premise discharged by the
faithful degree-`b` action of the original source. -/
theorem fusionEpimorphism_survival_card_le_schur_of_permutation_source
    (p : ℕ) [Fact p.Prime] {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b)))
    {Q B : Type} [Group Q] [Finite Q] [Group B] [Finite B]
    (pi : Q →* B) (hpi : Function.Surjective pi)
    (M : Rep (ZMod p) B) [Finite M]
    (E : OriginalKernelModuleChart pi M)
    (S : GroupEpimorphism J Q → Prop) :
    (Nat.card {f : GroupEpimorphism J Q // S f} : ℝ) ≤
      Nat.card (GroupEpimorphism J B) *
        (Nat.card M * Nat.card (groupCohomology.H1 M) *
          (p : ℝ) ^
            (representationSchurCapacity M.ρ * ((b : ℝ) / p))) := by
  let P : ∀ beta : GroupEpimorphism J B, Sylow p beta.1.ker :=
    fun _ => Classical.choice inferInstance
  apply fusionEpimorphism_survival_card_le_schur_of_rank_bound
    p pi hpi M E P S (b : ℝ)
  intro beta
  calc
    (Module.finrank (ZMod p)
        (PrimeAbelianization p (P beta : Subgroup beta.1.ker)) : ℝ)
        ≤ ((b / p : ℕ) : ℝ) := by
          exact_mod_cast
            originalQuotientKernelSylow_primeAbelianization_rank_le
              p J beta (P beta)
    _ ≤ (b : ℝ) / p := Nat.cast_div_le

universe u

/-! ## Faithful noncommutative simple modules have strict Schur capacity -/

/-- The original action commutes with every endomorphism of its full
monoid-algebra module, so it is linear over the Schur endomorphism ring. -/
def representationActionEndLinearMap
    {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A]
    (sigma : Representation k B A) (g : B) :
    Module.End (Module.End k[B] sigma.asModule) sigma.asModule where
  toFun x := MonoidAlgebra.single g (1 : k) • x
  map_add' x y := smul_add _ _ _
  map_smul' f x :=
    (f.map_smul (MonoidAlgebra.single g (1 : k)) x).symm

/-- The full representation, with scalars enlarged to its Schur
endomorphism ring. -/
def representationActionEndRepresentation
    {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A]
    (sigma : Representation k B A) :
    Representation (Module.End k[B] sigma.asModule) B sigma.asModule where
  toFun g := representationActionEndLinearMap sigma g
  map_one' := by
    ext x
    apply sigma.asModuleEquiv.injective
    simp [representationActionEndLinearMap, Representation.single_smul,
      Representation.asModuleEquiv]
    rfl
  map_mul' g h := by
    ext x
    apply sigma.asModuleEquiv.injective
    simp [representationActionEndLinearMap, Representation.single_smul,
      Representation.asModuleEquiv]
    rfl

/-- Enlarging the scalars to the Schur ring does not alter the kernel of the
literal group action. -/
theorem representationActionEndRepresentation_ker
    {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A]
    (sigma : Representation k B A) :
    (representationActionEndRepresentation sigma).ker = sigma.ker := by
  ext g
  constructor
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply DFunLike.ext _ _
    intro x
    have hx := LinearMap.congr_fun (MonoidHom.mem_ker.mp hg) x
    simpa [representationActionEndRepresentation,
      representationActionEndLinearMap] using hx
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro x
    have hx : sigma g x = x := by
      have hmap : sigma g = 1 := MonoidHom.mem_ker.mp hg
      exact DFunLike.congr_fun hmap x
    simpa [representationActionEndRepresentation,
      representationActionEndLinearMap] using hx

/-- A faithful irreducible representation of a noncommutative finite group
has Schur rank at least two.  Rank one would identify its endomorphism ring
with the ground finite division ring; Little Wedderburn then makes the unit
group commutative, contradicting faithful noncommutativity. -/
theorem two_le_schurRank_of_irreducible_faithful_noncommutative
    {k B A : Type u} [Field k] [Finite k] [Group B]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    (sigma : Representation k B A)
    (hirr : Representation.IsIrreducible sigma)
    (hfaithful : Function.Injective sigma)
    (hnoncomm : ¬ IsMulCommutative B) :
    2 ≤ Module.finrank (Module.End k[B] sigma.asModule) sigma.asModule := by
  classical
  letI : Representation.IsIrreducible sigma := hirr
  letI : Module k[B] sigma.asModule :=
    Representation.instModuleMonoidAlgebraAsModule sigma
  letI : IsScalarTower k k[B] sigma.asModule :=
    inferInstanceAs (IsScalarTower k k[B] (Representation.asModule sigma))
  letI : IsSimpleModule k[B] sigma.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule sigma).mp hirr
  letI : Nontrivial sigma.asModule :=
    IsSimpleModule.nontrivial k[B] sigma.asModule
  let E := Module.End k[B] sigma.asModule
  let d := Module.finrank E sigma.asModule
  have htower : Module.finrank k sigma.asModule =
      Module.finrank k E * d := by
    simpa [E, d] using
      (schur_simple_finrank_tower
        (k := k) (R := k[B]) (X := sigma.asModule))
  have hApos : 0 < Module.finrank k sigma.asModule := Module.finrank_pos
  have hprod : 0 < Module.finrank k E * d := by
    simpa [htower] using hApos
  have hEpos : 0 < Module.finrank k E :=
    pos_of_mul_pos_left hprod (Nat.zero_le d)
  have hdpos : 0 < d := pos_of_mul_pos_right hprod (Nat.zero_le _)
  letI : FiniteDimensional k E :=
    FiniteDimensional.of_finrank_pos hEpos
  letI : Finite E := Module.finite_of_finite k
  letI : Field E := littleWedderburn E
  letI : FiniteDimensional E sigma.asModule :=
    FiniteDimensional.of_finrank_pos hdpos
  by_contra htwo
  have hdlt : d < 2 := by
    apply Nat.lt_of_not_ge
    simpa [d] using htwo
  have hd1 : d = 1 := by omega
  have hEndFinrank : Module.finrank E (Module.End E sigma.asModule) = 1 := by
    rw [Module.finrank_linearMap, show Module.finrank E sigma.asModule = 1 by
      simpa [d] using hd1]
  let eEnd : E ≃+* Module.End E sigma.asModule :=
    RingEquiv.ofBijective (algebraMap E (Module.End E sigma.asModule))
      (Module.Free.bijective_algebraMap_of_finrank_eq_one
        (R := E) (S := Module.End E sigma.asModule) hEndFinrank)
  let rhoE := MonoidHom.toHomUnits
    (representationActionEndRepresentation sigma)
  have hker : rhoE.ker = ⊥ := by
    rw [MonoidHom.ker_toHomUnits,
      representationActionEndRepresentation_ker]
    exact (MonoidHom.ker_eq_bot_iff sigma).mpr hfaithful
  have hrho : Function.Injective rhoE :=
    (MonoidHom.ker_eq_bot_iff rhoE).mp hker
  apply hnoncomm
  refine ⟨⟨fun g h => hrho ?_⟩⟩
  apply Units.ext
  change (representationActionEndRepresentation sigma (g * h) :
      Module.End E sigma.asModule) =
    representationActionEndRepresentation sigma (h * g)
  rw [map_mul, map_mul]
  obtain ⟨x, hx⟩ := eEnd.surjective
    (representationActionEndRepresentation sigma g)
  obtain ⟨y, hy⟩ := eEnd.surjective
    (representationActionEndRepresentation sigma h)
  rw [← hx, ← hy, ← map_mul, mul_comm, map_mul]

/-- Irreducibility leaves only the whole module as a simple Schur row.  If
the representation is faithful and its group is noncommutative, the strict
rank-two conclusion gives Schur capacity at most one half. -/
theorem representationSchurCapacity_le_half_of_irreducible_faithful_noncommutative
    {k B A : Type u} [Field k] [Finite k] [Group B]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    (sigma : Representation k B A)
    (hirr : Representation.IsIrreducible sigma)
    (hfaithful : Function.Injective sigma)
    (hnoncomm : ¬ IsMulCommutative B) :
    representationSchurCapacity sigma ≤ (1 : ℝ) / 2 := by
  classical
  letI : Representation.IsIrreducible sigma := hirr
  unfold representationSchurCapacity schurCapacity
  apply csSup_le (Set.insert_nonempty _ _)
  rintro y (rfl | ⟨S, hS, rfl⟩)
  · norm_num
  · letI : Module k[B] sigma.asModule :=
      Representation.instModuleMonoidAlgebraAsModule sigma
    letI : IsScalarTower k k[B] sigma.asModule :=
      inferInstanceAs (IsScalarTower k k[B] (Representation.asModule sigma))
    letI : IsSimpleModule k[B] sigma.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule sigma).mp hirr
    letI : Nontrivial sigma.asModule :=
      IsSimpleModule.nontrivial k[B] sigma.asModule
    letI : IsSimpleModule k[B] S := hS
    haveI : Nontrivial S := IsSimpleModule.nontrivial k[B] S
    have hSne : S ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp inferInstance
    have hStop : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hSne
    subst S
    let e : (⊤ : Submodule k[B] sigma.asModule) ≃ₗ[k[B]] sigma.asModule :=
      Submodule.topEquiv
    letI : FiniteDimensional k (⊤ : Submodule k[B] sigma.asModule) :=
      FiniteDimensional.of_injective
        ((⊤ : Submodule k[B] sigma.asModule).subtype.restrictScalars k)
        (⊤ : Submodule k[B] sigma.asModule).subtype_injective
    have hHom : Module.finrank k
        ((⊤ : Submodule k[B] sigma.asModule) →ₗ[k[B]] sigma.asModule) =
        Module.finrank k (Module.End k[B] sigma.asModule) :=
      (schurHomCongrSource (k := k) (A := sigma.asModule) e).finrank_eq
    have hTop : Module.finrank k (⊤ : Submodule k[B] sigma.asModule) =
        Module.finrank k sigma.asModule :=
      (e.restrictScalars k).finrank_eq
    have htower := schur_simple_finrank_tower
      (k := k) (R := k[B]) (X := sigma.asModule)
    have hd2 := two_le_schurRank_of_irreducible_faithful_noncommutative
      sigma hirr hfaithful hnoncomm
    rw [hHom, hTop, htower]
    let f := Module.finrank k (Module.End k[B] sigma.asModule)
    let d := Module.finrank (Module.End k[B] sigma.asModule) sigma.asModule
    have hprodNat : 0 < f * d := by
      rw [← htower]
      exact Module.finrank_pos
    have hdenpos : (0 : ℝ) < f * d := by exact_mod_cast hprodNat
    rw [Nat.cast_mul]
    apply (div_le_iff₀ (by simpa [f, d] using hdenpos)).mpr
    have hfd' : (f : ℝ) * 2 ≤ f * d := by
      exact_mod_cast (show f * 2 ≤ f * d by
        exact Nat.mul_le_mul_left f (by simpa [d] using hd2))
    have hfd : (2 : ℝ) * f ≤ f * d := by nlinarith
    simpa [f, d] using (show (f : ℝ) ≤ (1 / 2 : ℝ) * (f * d) by
      nlinarith)

/-- A finite-dimensional simple target has Schur capacity at most one.
The possible division endomorphism ring causes no loss: the tower law says
its base-field dimension is at most the dimension of the simple module. -/
theorem schurCapacity_le_one_of_simple
    {k R A : Type u} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
    [FiniteDimensional k A] [IsSimpleModule R A] :
    schurCapacity k R A ≤ 1 := by
  classical
  letI : Nontrivial A := IsSimpleModule.nontrivial R A
  unfold schurCapacity
  apply csSup_le (Set.insert_nonempty _ _)
  rintro y (rfl | ⟨S, hS, rfl⟩)
  · norm_num
  · letI : IsSimpleModule R S := hS
    haveI : Nontrivial S := IsSimpleModule.nontrivial R S
    have hSne : S ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp inferInstance
    have hStop : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hSne
    subst S
    let e : (⊤ : Submodule R A) ≃ₗ[R] A := Submodule.topEquiv
    letI : FiniteDimensional k (⊤ : Submodule R A) :=
      FiniteDimensional.of_injective
        ((⊤ : Submodule R A).subtype.restrictScalars k)
        (⊤ : Submodule R A).subtype_injective
    have hHom : Module.finrank k ((⊤ : Submodule R A) →ₗ[R] A) =
        Module.finrank k (Module.End R A) :=
      (schurHomCongrSource (k := k) (A := A) e).finrank_eq
    have hTop : Module.finrank k (⊤ : Submodule R A) =
        Module.finrank k A := (e.restrictScalars k).finrank_eq
    have hEnd : Module.finrank k (Module.End R A) ≤ Module.finrank k A := by
      have htower := schur_simple_finrank_tower (k := k) (R := R) (X := A)
      have hAposNat : 0 < Module.finrank k A :=
        Module.finrank_pos (R := k) (M := A)
      have hprod : 0 < Module.finrank k (Module.End R A) *
          Module.finrank (Module.End R A) A := by
        rw [← htower]
        exact hAposNat
      have hpos : 0 < Module.finrank (Module.End R A) A := by
        exact pos_of_mul_pos_right hprod (Nat.zero_le _)
      calc
        Module.finrank k (Module.End R A) ≤
            Module.finrank k (Module.End R A) *
              Module.finrank (Module.End R A) A :=
          Nat.le_mul_of_pos_right _ hpos
        _ = Module.finrank k A := htower.symm
    rw [hHom, hTop]
    have hApos : (0 : ℝ) < Module.finrank k A := by
      exact_mod_cast Module.finrank_pos (R := k) (M := A)
    apply (div_le_iff₀ hApos).mpr
    simpa only [one_mul] using (show
      (Module.finrank k (Module.End R A) : ℝ) ≤ Module.finrank k A by
        exact_mod_cast hEnd)

/-- Representation form of the simple-target capacity bound. -/
theorem representationSchurCapacity_le_one_of_irreducible
    {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    (sigma : Representation k B A) (hirr : Representation.IsIrreducible sigma) :
    representationSchurCapacity sigma ≤ 1 := by
  letI : Representation.IsIrreducible sigma := hirr
  unfold representationSchurCapacity
  letI : Module k[B] sigma.asModule :=
    Representation.instModuleMonoidAlgebraAsModule sigma
  letI : IsScalarTower k k[B] sigma.asModule :=
    inferInstanceAs (IsScalarTower k k[B] (Representation.asModule sigma))
  letI : IsSimpleModule k[B] sigma.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule sigma).mp hirr
  exact schurCapacity_le_one_of_simple

namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [Finite L] [MulAction L Ω] [Finite Ω]
  [Nontrivial Ω] [FaithfulSMul L Ω]
  (P : PrimitiveAffineProfile L Ω)

/-- The canonical affine projection is the identity on the literal point
stabilizer. -/
@[simp] theorem complementProjection_complement (x : Ω)
    (h : P.complement x) :
    P.complementProjection x (h : L) = h := by
  have hs : (P.semidirectEquiv x).symm (h : L) =
      SemidirectProduct.inr h := by
    apply (P.semidirectEquiv x).injective
    rw [(P.semidirectEquiv x).apply_symm_apply]
    simp [semidirectEquiv, SemidirectProduct.mulEquivSubgroup]
  change ((P.semidirectEquiv x).symm (h : L)).right = h
  rw [hs]
  rfl

/-- Conjugation by an affine element on translations depends only on its
literal point-stabilizer projection.  The discarded translation commutes
with every translation; this is where elementary abelianness, already forced
by primitivity, is used. -/
theorem complementAction_projection
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (q : L) (v : P.V) :
    P.complementAction x (P.complementProjection x q) v =
      MulAut.conjNormal q v := by
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  let h : P.complement x := P.complementProjection x q
  have hu_mem : q * (h : L)⁻¹ ∈ P.V := by
    rw [← P.complementProjection_ker x, MonoidHom.mem_ker]
    simp [h]
  let u : P.V := ⟨q * (h : L)⁻¹, hu_mem⟩
  have hq : q = (u : L) * (h : L) := by
    simp [u]
  let z : P.V := MulAut.conjNormal (h : L) v
  have hcomm : (u : L) * (z : L) = (z : L) * (u : L) := by
    exact congrArg Subtype.val (mul_comm u z)
  apply Subtype.ext
  change (h : L) * (v : L) * (h : L)⁻¹ = q * (v : L) * q⁻¹
  rw [hq]
  symm
  calc
    ((u : L) * (h : L)) * (v : L) * ((u : L) * (h : L))⁻¹ =
        (u : L) * ((h : L) * (v : L) * (h : L)⁻¹) * (u : L)⁻¹ := by
          group
    _ = (u : L) * (z : L) * (u : L)⁻¹ := by rfl
    _ = (z : L) := by rw [hcomm]; group
    _ = (h : L) * (v : L) * (h : L)⁻¹ := by rfl

/-- The actual point stabilizer representation on the elementary translation
module.  It is constructed from literal conjugation and the structural chart,
not supplied by a catalogue row. -/
theorem complementAction_preserves_equiv_ker
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω)
    (h : P.complement x) (v : P.V) (hv : C.equiv v = 1) :
    C.equiv (P.complementAction x h v) = 1 := by
  have hv1 : v = 1 := by
    apply C.equiv.injective
    rw [hv, map_one]
  rw [hv1, map_one, map_one]

abbrev complementRepresentation
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω) :
    Rep (ZMod P.p) (P.complement x) := by
  letI : Fact P.p.Prime := C.primeFact
  exact Rep.of (elementaryQuotientRepresentation (p := P.p)
    (R := P.V) (V := C.V)
    (P.complementAction x) C.equiv.toMonoidHom C.equiv.surjective
      (P.complementAction_preserves_equiv_ker hprimitive C x))

theorem complementRepresentation_apply
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω)
    (h : P.complement x) (v : C.V) :
    (P.complementRepresentation hprimitive C x).ρ h v =
      (C.equiv (P.complementAction x h
        (C.equiv.symm (Multiplicative.ofAdd v)))).toAdd := by
  letI : Fact P.p.Prime := C.primeFact
  change (elementaryQuotientRepresentation (p := P.p)
    (R := P.V) (V := C.V)
    (P.complementAction x) C.equiv.toMonoidHom C.equiv.surjective
      (P.complementAction_preserves_equiv_ker hprimitive C x)) h v = _
  symm
  have he := elementaryQuotientRepresentation_equivariant (p := P.p)
      (P.complementAction x) C.equiv.toMonoidHom C.equiv.surjective
      (P.complementAction_preserves_equiv_ker hprimitive C x) h
      (C.equiv.symm (Multiplicative.ofAdd v))
  convert he using 1
  · simp

/-- The elementary translation chart, now regarded as the exact kernel of
the canonical affine projection. -/
def bottomKernelEquiv
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω) :
    Multiplicative C.V ≃* (P.complementProjection x).ker :=
  C.equiv.symm.trans
    (MulEquiv.subgroupCongr (P.complementProjection_ker x).symm)

@[simp] theorem bottomKernelEquiv_coe
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω)
    (v : Multiplicative C.V) :
    ((P.bottomKernelEquiv hprimitive C x v :
      (P.complementProjection x).ker) : L) = (C.equiv.symm v : P.V) := by
  rfl

/-- Exact original kernel chart for the affine extension by its point
stabilizer. -/
def bottomModuleChart
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω) :
    OriginalKernelModuleChart (P.complementProjection x)
      (P.complementRepresentation hprimitive C x) where
  equiv := P.bottomKernelEquiv hprimitive C x
  conjugate q v := by
    change ((P.bottomKernelEquiv hprimitive C x
      (Multiplicative.ofAdd
        ((P.complementRepresentation hprimitive C x).ρ
          (P.complementProjection x q) v)) :
            (P.complementProjection x).ker) : L) = _
    rw [P.bottomKernelEquiv_coe, P.complementRepresentation_apply]
    simp only [ofAdd_toAdd, C.equiv.symm_apply_apply]
    have hp := P.complementAction_projection hprimitive x q
      (C.equiv.symm (Multiplicative.ofAdd v))
    rw [hp]
    rw [P.bottomKernelEquiv_coe]
    rfl

/-! ## Primitivity gives a simple complement module -/

/-- The translation subgroup cut out by a complement-invariant linear
subspace. -/
def subrepresentationTranslationSubgroup
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω)
    (W : Subrepresentation
      (P.complementRepresentation hprimitive C x).ρ) : Subgroup P.V :=
  W.toSubmodule.toAddSubgroup.toSubgroup.comap C.equiv.toMonoidHom

@[simp] theorem mem_subrepresentationTranslationSubgroup
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω)
    (W : Subrepresentation
      (P.complementRepresentation hprimitive C x).ρ) (v : P.V) :
    v ∈ P.subrepresentationTranslationSubgroup hprimitive C x W ↔
      (C.equiv v).toAdd ∈ W := by
  rfl

/-- A primitive affine action makes its translation module irreducible for
the actual point stabilizer.  The proof sends an invariant subspace back to
an ambient normal subgroup and invokes the already-proved minimal normality
of the regular translation group. -/
theorem complementRepresentation_irreducible
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω) :
    letI : Fact P.p.Prime := C.primeFact
    Representation.IsIrreducible
      (P.complementRepresentation hprimitive C x).ρ := by
  letI : Fact P.p.Prime := C.primeFact
  let ρ := (P.complementRepresentation hprimitive C x).ρ
  have hbot_top : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    obtain ⟨a, ha⟩ := exists_ne (0 : C.V)
    intro h
    have hamem : a ∈ (⊥ : Subrepresentation ρ) := by
      rw [h]
      trivial
    change a ∈ (⊥ : Submodule (ZMod P.p) C.V) at hamem
    exact ha ((Submodule.mem_bot (R := ZMod P.p)).mp hamem)
  letI : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbot_top⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  let K₀ : Subgroup P.V :=
    P.subrepresentationTranslationSubgroup hprimitive C x W
  let K : Subgroup L := K₀.map P.V.subtype
  have hKnormal : K.Normal := by
    constructor
    intro y hy q
    obtain ⟨v, hv, rfl⟩ := hy
    have hvW : (C.equiv v).toAdd ∈ W :=
      (P.mem_subrepresentationTranslationSubgroup hprimitive C x W v).mp hv
    have hact := W.apply_mem_toSubmodule (P.complementProjection x q) hvW
    rw [P.complementRepresentation_apply] at hact
    refine ⟨MulAut.conjNormal q v, ?_, rfl⟩
    apply (P.mem_subrepresentationTranslationSubgroup hprimitive C x W _).mpr
    rw [← P.complementAction_projection hprimitive x q v]
    simpa only [ofAdd_toAdd, C.equiv.symm_apply_apply] using hact
  have hKle : K ≤ P.V := Subgroup.map_subtype_le K₀
  have hK := P.minimal hprimitive K hKnormal hKle
  have hK₀ : K₀ = ⊥ ∨ K₀ = ⊤ := by
    rcases hK with hbot | htop
    · left
      exact (K₀.map_eq_bot_iff_of_injective P.V.subtype_injective).mp hbot
    · right
      apply Subgroup.map_injective P.V.subtype_injective
      simpa only [K, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using htop
  rcases hK₀ with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    apply SetLike.ext
    intro a
    constructor
    · intro ha
      let v : P.V := C.equiv.symm (Multiplicative.ofAdd a)
      have hv : v ∈ K₀ :=
        (P.mem_subrepresentationTranslationSubgroup hprimitive C x W v).mpr (by
          simpa [v] using ha)
      rw [hbot] at hv
      have hv1 : v = 1 := Subgroup.mem_bot.mp hv
      have ha0 : a = 0 := by
        apply Multiplicative.ofAdd.injective
        calc
          Multiplicative.ofAdd a = C.equiv v := by simp [v]
          _ = C.equiv 1 := congrArg C.equiv hv1
          _ = Multiplicative.ofAdd 0 := by simp
      subst a
      exact Submodule.zero_mem _
    · intro ha
      have ha0 : a = 0 := (Submodule.mem_bot (R := ZMod P.p)).mp ha
      subst a
      exact Submodule.zero_mem _
  · right
    apply Subrepresentation.toSubmodule_injective
    apply SetLike.ext
    intro a
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      let v : P.V := C.equiv.symm (Multiplicative.ofAdd a)
      have hv : v ∈ K₀ := by rw [htop]; exact Subgroup.mem_top v
      have hvW :=
        (P.mem_subrepresentationTranslationSubgroup hprimitive C x W v).mp hv
      simpa [v] using hvW

/-- The exact complement representation retains the faithful conjugation
action of the literal point stabilizer. -/
theorem complementRepresentation_injective
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω) :
    letI : Fact P.p.Prime := C.primeFact
    Function.Injective (P.complementRepresentation hprimitive C x).ρ := by
  letI : Fact P.p.Prime := C.primeFact
  rw [injective_iff_map_eq_one]
  intro h hh
  apply P.complementAction_injective x
  apply MulEquiv.ext
  intro v
  apply C.equiv.injective
  apply Multiplicative.toAdd.injective
  have hz := DFunLike.congr_fun hh (C.equiv v).toAdd
  rw [P.complementRepresentation_apply] at hz
  simpa using hz

/-- The primitive translation module has intrinsic Schur capacity at most
one. -/
theorem complementRepresentation_schurCapacity_le_one
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω) :
    letI : Fact P.p.Prime := C.primeFact
    representationSchurCapacity
      (P.complementRepresentation hprimitive C x).ρ ≤ 1 := by
  letI : Fact P.p.Prime := C.primeFact
  exact representationSchurCapacity_le_one_of_irreducible _
    (P.complementRepresentation_irreducible hprimitive C x)

/-- Nonsolubility in particular rules out commutativity. -/
theorem noncommutative_of_not_isSolvable
    {G : Type u} [Group G] (h : ¬ IsSolvable G) :
    ¬ IsMulCommutative G := by
  intro hcomm
  apply h
  exact isSolvable_of_comm (fun a b => hcomm.is_comm.comm a b)

/-- A noncommutative affine complement has the strict Schur-capacity bound
needed by the nonsoluble primitive-affine family. -/
theorem complementRepresentation_schurCapacity_le_half
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω)
    (hnoncomm : ¬ IsMulCommutative (P.complement x)) :
    letI : Fact P.p.Prime := C.primeFact
    representationSchurCapacity
      (P.complementRepresentation hprimitive C x).ρ ≤ (1 : ℝ) / 2 := by
  letI : Fact P.p.Prime := C.primeFact
  exact
    representationSchurCapacity_le_half_of_irreducible_faithful_noncommutative
      _ (P.complementRepresentation_irreducible hprimitive C x)
      (P.complementRepresentation_injective hprimitive C x) hnoncomm

/-- Closed count for the bottom affine quotient.  The source-rank theorem,
the exact original kernel chart, primitive irreducibility, and the Schur
division-ring estimate are all discharged.  Only the literal point-stabilizer
quotient maps and the fixed target's translation and `H¹` constants remain. -/
theorem bottom_epimorphism_card_le_schur_one
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J L) : ℝ) ≤
      Nat.card (GroupEpimorphism J (P.complement x)) *
        (Nat.card C.V *
          Nat.card (groupCohomology.H1
            (P.complementRepresentation hprimitive C x)) *
          (P.p : ℝ) ^ ((b : ℝ) / P.p)) := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  let M := P.complementRepresentation hprimitive C x
  have h := fusionEpimorphism_survival_card_le_schur_of_permutation_source
    P.p J (P.complementProjection x) (P.complementProjection_surjective x)
      M (P.bottomModuleChart hprimitive C x) (fun _ => True)
  have hcard : Nat.card {f : GroupEpimorphism J L // True} =
      Nat.card (GroupEpimorphism J L) := by simp
  rw [hcard] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Fact.out : P.p.Prime).one_lt.le
  · have hb : 0 ≤ (b : ℝ) / P.p := by positivity
    have hc := P.complementRepresentation_schurCapacity_le_one hprimitive C x
    simpa [M] using mul_le_mul_of_nonneg_right hc hb

/-- Strict bottom-fibre count for a noncommutative affine complement.  This
is the original-source form used in the nonsoluble affine envelope. -/
theorem bottom_epimorphism_card_le_schur_half
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (C : P.ElementaryChart hprimitive) (x : Ω)
    (hnoncomm : ¬ IsMulCommutative (P.complement x))
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J L) : ℝ) ≤
      Nat.card (GroupEpimorphism J (P.complement x)) *
        (Nat.card C.V *
          Nat.card (groupCohomology.H1
            (P.complementRepresentation hprimitive C x)) *
          (P.p : ℝ) ^ (((1 : ℝ) / 2) * ((b : ℝ) / P.p))) := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  let M := P.complementRepresentation hprimitive C x
  have h := fusionEpimorphism_survival_card_le_schur_of_permutation_source
    P.p J (P.complementProjection x) (P.complementProjection_surjective x)
      M (P.bottomModuleChart hprimitive C x) (fun _ => True)
  have hcard : Nat.card {f : GroupEpimorphism J L // True} =
      Nat.card (GroupEpimorphism J L) := by simp
  rw [hcard] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Fact.out : P.p.Prime).one_lt.le
  · have hb : 0 ≤ (b : ℝ) / P.p := by positivity
    have hc := P.complementRepresentation_schurCapacity_le_half
      hprimitive C x hnoncomm
    simpa [M] using mul_le_mul_of_nonneg_right hc hb

end PrimitiveAffineProfile

end SymmetricSubgroupAsymptotics

end
