import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRelativeKernelAnchor
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitRegistry
import SymmetricSubgroupAsymptotics.RepresentationSchurRows
import SymmetricSubgroupAsymptotics.SemisimpleModuleGenerators
import SymmetricSubgroupAsymptotics.TraceyPrimePowerInput
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Order.Atoms.Finite

/-!
# Relative characters from normal orbits in a binary kernel

The paired-eight argument does not need a basis-sized tuple of characters
of its binary direct kernel.  It needs one irreducible character for each
normal-generator slot of the kernel's central involution module.  This file
isolates that reduction.

For each slot, an irreducible representation of the binary kernel is lifted
to an irreducible representation of the whole quotient by Frobenius
reciprocity and Maschke.  Normality of the overgroup kernel then makes the
whole conjugacy orbit of the chosen kernel representation visible.  If the
displayed kernel irreducibles separate central involutions after all ambient
conjugates, the lifted whole-group irreducibles are jointly faithful on the
kernel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {Q B : Type*} [Group Q] [Finite Q] [Group B]

/-- Ambient conjugation preserves the intrinsic central involutions of a
normal kernel.  We construct the result through the literal ambient omega
subgroup, whose normality has already been proved. -/
noncomputable def binaryKernelOmegaConjugateOmega
    (pi : Q →* B) (q : Q) (z : binaryCentralOmega pi.ker) :
    binaryCentralOmega pi.ker := by
  let e := binaryCentralOmegaEquivNormalKernel pi
  let z' : normalKernelCentralOmega pi := e z
  exact e.symm
    ⟨q * (z' : Q) * q⁻¹,
      Subgroup.Normal.conj_mem inferInstance (z' : Q) z'.2 q⟩

/-- The same conjugate, regarded as an element of the normal kernel. -/
noncomputable def binaryKernelOmegaConjugate
    (pi : Q →* B) (q : Q) (z : binaryCentralOmega pi.ker) : pi.ker :=
  binaryCentralOmegaEmbedding (binaryKernelOmegaConjugateOmega pi q z)

@[simp] theorem binaryKernelOmegaConjugate_val
    (pi : Q →* B) (q : Q) (z : binaryCentralOmega pi.ker) :
    (binaryKernelOmegaConjugate pi q z : Q) =
      q * (binaryCentralOmegaEmbedding z : Q) * q⁻¹ :=
  by
    let e := binaryCentralOmegaEquivNormalKernel pi
    let z' : normalKernelCentralOmega pi := e z
    let y : normalKernelCentralOmega pi :=
      ⟨q * (z' : Q) * q⁻¹,
        Subgroup.Normal.conj_mem inferInstance (z' : Q) z'.2 q⟩
    have h := congrArg (fun x : normalKernelCentralOmega pi ↦ (x : Q))
      (e.apply_symm_apply y)
    simpa only [binaryKernelOmegaConjugate,
      binaryKernelOmegaConjugateOmega, e, z', y] using h

@[simp] theorem binaryKernelOmegaConjugateOmega_one
    (pi : Q →* B) (z : binaryCentralOmega pi.ker) :
    binaryKernelOmegaConjugateOmega pi 1 z = z := by
  apply binaryCentralOmegaEmbedding_injective
  apply Subtype.ext
  rw [binaryKernelOmegaConjugate_val]
  simp

@[simp] theorem binaryKernelOmegaConjugateOmega_mul
    (pi : Q →* B) (q q' : Q) (z : binaryCentralOmega pi.ker) :
    binaryKernelOmegaConjugateOmega pi (q * q') z =
      binaryKernelOmegaConjugateOmega pi q
        (binaryKernelOmegaConjugateOmega pi q' z) := by
  apply binaryCentralOmegaEmbedding_injective
  apply Subtype.ext
  change (binaryKernelOmegaConjugate pi (q * q') z : Q) =
    (binaryKernelOmegaConjugate pi q
      (binaryKernelOmegaConjugateOmega pi q' z) : Q)
  rw [binaryKernelOmegaConjugate_val, binaryKernelOmegaConjugate_val,
    binaryKernelOmegaConjugate_val]
  group

/-- Ambient conjugation as an automorphic action on the intrinsic central
omega of the binary kernel. -/
noncomputable def binaryKernelOmegaConjugationHom
    (pi : Q →* B) (q : Q) :
    binaryCentralOmega pi.ker →* binaryCentralOmega pi.ker where
  toFun := binaryKernelOmegaConjugateOmega pi q
  map_one' := by
    apply binaryCentralOmegaEmbedding_injective
    apply Subtype.ext
    rw [binaryKernelOmegaConjugate_val]
    simp
  map_mul' z w := by
    apply binaryCentralOmegaEmbedding_injective
    apply Subtype.ext
    change (binaryKernelOmegaConjugate pi q (z * w) : Q) =
      (binaryKernelOmegaConjugate pi q z : Q) *
        (binaryKernelOmegaConjugate pi q w : Q)
    rw [binaryKernelOmegaConjugate_val, binaryKernelOmegaConjugate_val,
      binaryKernelOmegaConjugate_val]
    group

/-- The binary linear representation obtained from ambient conjugation on
the central involutions of the kernel. -/
noncomputable def binaryKernelOmegaConjugationRepresentation
    (pi : Q →* B) :
    Representation (ZMod 2) Q (Additive (binaryCentralOmega pi.ker)) where
  toFun q :=
    (binaryKernelOmegaConjugationHom pi q).toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro z
    apply Additive.toMul.injective
    exact binaryKernelOmegaConjugateOmega_one pi (Additive.toMul z)
  map_mul' q q' := by
    apply LinearMap.ext
    intro z
    apply Additive.toMul.injective
    exact binaryKernelOmegaConjugateOmega_mul pi q q' (Additive.toMul z)

@[simp] theorem binaryKernelOmegaConjugationRepresentation_apply
    (pi : Q →* B) (q : Q) (z : binaryCentralOmega pi.ker) :
    binaryKernelOmegaConjugationRepresentation pi q (Additive.ofMul z) =
      Additive.ofMul (binaryKernelOmegaConjugateOmega pi q z) :=
  rfl

/-- Module generators over the group algebra are equivalently an ordinary
spanning family of their literal group orbits.  The forward direction is
the one needed for central-omega dual characters. -/
theorem orbit_span_eq_top_of_representationGeneratedBy
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) {r : ℕ}
    (hgen : RepresentationGeneratedBy rho r) :
    ∃ representative : Fin r → V,
      Submodule.span k
        (Set.range (fun iq : Fin r × G ↦
          rho iq.2 (representative iq.1))) = ⊤ := by
  obtain ⟨code, hcode⟩ := hgen
  let representative : Fin r → V := fun i ↦ rho.asModuleEquiv (code i)
  let orbit : Fin r × G → V := fun iq ↦
    rho iq.2 (representative iq.1)
  let W : Submodule k V := Submodule.span k (Set.range orbit)
  let S : Subrepresentation rho :=
    { toSubmodule := W
      apply_mem_toSubmodule := by
        intro g x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
            obtain ⟨⟨i, h⟩, rfl⟩ := hx
            have heq : rho g (rho h (representative i)) =
                rho (g * h) (representative i) := by
              simp only [map_mul, Module.End.mul_apply]
            rw [heq]
            exact Submodule.subset_span ⟨(i, g * h), rfl⟩
        | zero => simpa using W.zero_mem
        | add x y _ _ hx hy => simpa only [map_add] using W.add_mem hx hy
        | smul a x _ hx => simpa only [map_smul] using W.smul_mem a hx }
  have hgenerator (i : Fin r) : code i ∈ S.asSubmodule := by
    change representative i ∈ W
    apply Submodule.subset_span
    exact ⟨(i, 1), by simp only [orbit, map_one, Module.End.one_apply]⟩
  have hspan : Submodule.span k[G] (Set.range code) ≤ S.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hgenerator i
  have hS : S.asSubmodule = ⊤ := by
    apply top_unique
    rw [← hcode]
    exact hspan
  refine ⟨representative, ?_⟩
  change W = ⊤
  apply top_unique
  intro x _
  have hx : rho.asModuleEquiv.symm x ∈ S.asSubmodule := by
    rw [hS]
    exact Submodule.mem_top
  have hx' : rho.asModuleEquiv (rho.asModuleEquiv.symm x) ∈
      S.toSubmodule := by
    exact hx
  simpa only [LinearEquiv.apply_symm_apply] using hx'

/-- The module-theoretic socle of a representation: the sum of all simple
submodules of its group-algebra module. -/
noncomputable def representationSocleModule
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) : Submodule k[G] rho.asModule :=
  sSup {S : Submodule k[G] rho.asModule | IsSimpleModule k[G] S}

/-- The sum of all minimal nonzero invariant subspaces of a finite
representation.  This canonical detecting subrepresentation is the module
socle used by the paired-eight argument. -/
noncomputable def finiteRepresentationSocle
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Finite V]
    (rho : Representation k G V) : Subrepresentation rho :=
  Subrepresentation.ofSubmodule' (representationSocleModule rho)

theorem isAtom_le_finiteRepresentationSocle
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Finite V]
    {rho : Representation k G V}
    (S : Subrepresentation rho) (hS : IsAtom S) :
    S ≤ finiteRepresentationSocle rho := by
  change S.asSubmodule ≤ representationSocleModule rho
  apply le_sSup
  change IsSimpleModule k[G] S.asSubmodule
  rw [isSimpleModule_iff_isAtom]
  exact
    ((Subrepresentation.subrepresentationSubmoduleOrderIso
      (rho := rho)).isAtom_iff S).mpr hS

/-- The module socle is semisimple by construction: it is generated by
simple submodules of the ambient representation module. -/
theorem representationSocleModule_isSemisimple
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) :
    IsSemisimpleModule k[G] (representationSocleModule rho) := by
  rw [representationSocleModule, sSup_eq_iSup]
  apply isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
  intro S hS
  change IsSimpleModule k[G] S at hS
  letI : IsSimpleModule k[G] S := hS
  infer_instance

/-- The canonical socle subrepresentation carries the same semisimple
group-algebra module structure. -/
theorem finiteRepresentationSocle_isSemisimple
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Finite V]
    (rho : Representation k G V) :
    IsSemisimpleModule k[G]
      (finiteRepresentationSocle rho).toRepresentation.asModule := by
  exact
    ((submoduleRepresentationModuleEquiv rho
      (representationSocleModule rho)).isSemisimpleModule_iff).mp
        (representationSocleModule_isSemisimple rho)

/-! The invariant-subspace lattice of a finite-dimensional dual is the
order dual of the original invariant-subspace lattice.  Keeping the
annihilator construction at the representation level lets semisimplicity
of the canonical socle pass to the dual used by the Schur-capacity
endpoint. -/

/-- The annihilator of an invariant subspace is invariant under the
contragredient representation. -/
noncomputable def representationDualAnnihilator
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (S : Subrepresentation rho) :
    Subrepresentation rho.dual where
  toSubmodule := S.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g f hf := by
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro x hx
    change f (rho g⁻¹ x) = 0
    exact hf _ (S.apply_mem_toSubmodule g⁻¹ hx)

/-- The coannihilator of a dual invariant subspace is invariant in the
original representation. -/
noncomputable def representationDualCoannihilator
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (T : Subrepresentation rho.dual) :
    Subrepresentation rho where
  toSubmodule := T.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g x hx := by
    rw [Submodule.mem_dualCoannihilator] at hx ⊢
    intro f hf
    have h := hx (rho.dual g⁻¹ f)
      (T.apply_mem_toSubmodule g⁻¹ hf)
    simpa only [Representation.dual_apply,
      Module.Dual.transpose_apply, inv_inv] using h

/-- Finite-dimensional duality reverses the invariant-subspace lattice. -/
noncomputable def subrepresentationDualOrderIso
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) :
    Subrepresentation rho ≃o (Subrepresentation rho.dual)ᵒᵈ where
  toFun S := OrderDual.toDual (representationDualAnnihilator rho S)
  invFun T := representationDualCoannihilator rho (OrderDual.ofDual T)
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    exact Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv T := by
    apply Subrepresentation.toSubmodule_injective
    exact Subspace.dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := by
    intro S T
    change T.toSubmodule.dualAnnihilator ≤
        S.toSubmodule.dualAnnihilator ↔ S.toSubmodule ≤ T.toSubmodule
    exact Subspace.dualAnnihilator_le_dualAnnihilator_iff

/-- A finite-dimensional dual of a semisimple representation is
semisimple, over an arbitrary field and with no Maschke hypothesis. -/
theorem representationDual_isSemisimple
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V)
    [IsSemisimpleModule k[G] rho.asModule] :
    IsSemisimpleModule k[G] rho.dual.asModule := by
  have hrep : Representation.IsSemisimpleRepresentation rho :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
      rho).mpr inferInstance
  letI : ComplementedLattice (Subrepresentation rho) := hrep
  have hdualOrder :
      ComplementedLattice ((Subrepresentation rho.dual)ᵒᵈ) :=
    (subrepresentationDualOrderIso rho).complementedLattice
  have hdualRep : Representation.IsSemisimpleRepresentation rho.dual := by
    constructor
    intro T
    let Td : (Subrepresentation rho.dual)ᵒᵈ := OrderDual.toDual T
    obtain ⟨Ud, hTU⟩ := hdualOrder.exists_isCompl Td
    exact ⟨OrderDual.ofDual Ud, hTU.dual⟩
  exact
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
      rho.dual).mp hdualRep

/-- A fixed-row dimension bound together with the matching Schur-scaled
multiplicity bound on every nonfixed simple row controls the full Schur
capacity.  The shared factor `finrank End(S) S` is essential: it is what
lets repeated copies of one nontrivial simple type share generator
positions. -/
theorem representationSchurCapacity_le_of_fixed_nonfixed_multiplicity
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) (cap : ℕ)
    (hfixed : Module.finrank k rho.invariants ≤ cap)
    (hnonfixed : ∀ S : Submodule k[G] rho.asModule,
      [IsSimpleModule k[G] S] →
      ¬ representationSubmoduleFixed rho S →
      schurSocleMultiplicity
          (k := k) (R := k[G]) (A := rho.asModule) (X := S) ≤
        cap * Module.finrank (Module.End k[G] S) S) :
    representationSchurCapacity rho ≤ cap := by
  unfold representationSchurCapacity schurCapacity
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨S, hS, rfl⟩)
  · positivity
  · letI : IsSimpleModule k[G] S := hS
    letI : Nontrivial S := IsSimpleModule.nontrivial k[G] S
    letI : FiniteDimensional k S :=
      FiniteDimensional.of_injective
        (S.subtype.restrictScalars k) S.subtype_injective
    by_cases hSfixed : representationSubmoduleFixed rho S
    · exact (schurSimpleRatio_le_invariants_of_fixed rho S hSfixed).trans
        (by exact_mod_cast hfixed)
    · rw [schurSimpleRatio_eq_multiplicity_division
        (k := k) (R := k[G]) (A := rho.asModule) (X := S)]
      have hepos : 0 < Module.finrank (Module.End k[G] S) S := by
        have hspos : 0 < Module.finrank k S :=
          Module.finrank_pos (R := k) (M := S)
        have htower := schur_simple_finrank_tower
          (k := k) (R := k[G]) (X := S)
        by_contra he
        have hezero : Module.finrank (Module.End k[G] S) S = 0 :=
          Nat.eq_zero_of_not_pos he
        rw [htower, hezero, mul_zero] at hspos
        omega
      have heposR :
          (0 : ℝ) < Module.finrank (Module.End k[G] S) S := by
        exact_mod_cast hepos
      apply (div_le_iff₀ heposR).mpr
      exact_mod_cast hnonfixed S hSfixed

/-- Every nonzero cyclic orbit meets the finite representation socle.
Equivalently, the socle is an essential subrepresentation. -/
theorem finiteRepresentationSocle_essential
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Finite V]
    (rho : Representation k G V) (x : V) (hx0 : x ≠ 0) :
    ∃ y : (finiteRepresentationSocle rho).toSubmodule, y ≠ 0 ∧
      (y : V) ∈ binaryOrbitSpan rho x := by
  let W : Subrepresentation rho := orbitSubrepresentation rho x
  have hW : W ≠ ⊥ := by
    intro hbot
    have hx : x ∈ W.toSubmodule := binaryOrbitSpan_point rho x
    rw [hbot] at hx
    exact hx0 (by simpa only [Submodule.mem_bot] using hx)
  obtain ⟨S, hS, hSW⟩ :=
    (eq_bot_or_exists_atom_le W).resolve_left hW
  obtain ⟨y, hyS, hyBot⟩ := SetLike.exists_of_lt hS.bot_lt
  have hy0 : y ≠ 0 := by
    intro hy
    apply hyBot
    subst y
    exact Submodule.zero_mem _
  let ys : (finiteRepresentationSocle rho).toSubmodule :=
    ⟨y, isAtom_le_finiteRepresentationSocle S hS hyS⟩
  refine ⟨ys, ?_, ?_⟩
  · intro hys
    apply hy0
    exact congrArg Subtype.val hys
  · exact hSW hyS

/-- A tuple of irreducible kernel representations whose ambient conjugacy
orbits separate the intrinsic central involutions.  This is the exact
semantic output required from a finite dual-orbit certificate. -/
structure BinaryKernelOmegaOrbitIrreducibles
    (pi : Q →* B) (r : ℕ) : Type 1 where
  fibre : Fin r → FiniteIrreducibleRepresentation ℂ pi.ker
  separates : ∀ z : binaryCentralOmega pi.ker,
    (∀ i q, (fibre i).action (binaryKernelOmegaConjugate pi q z) = 1) →
      z = 1

/-- A character form of the same finite certificate.  Characters are kept
on the literal central-omega subgroup of the binary kernel, so existing
central-character machinery constructs the kernel irreducibles without a
new representation model. -/
structure BinaryKernelOmegaOrbitCharacters
    (pi : Q →* B) (r : ℕ) : Type where
  character : Fin r → binaryOmegaSubgroup pi.ker →* ℂ
  separates : ∀ z : binaryCentralOmega pi.ker,
    (∀ i q, character i
      (binaryOmegaSubgroupEquiv
        (binaryKernelOmegaConjugateOmega pi q z)) = 1) → z = 1

/-- Finite coordinate form of an orbit certificate.  A producer selects
canonical dual-basis coordinates of the intrinsic central omega module and
checks that their ambient conjugates detect every central involution. -/
structure BinaryKernelOmegaCoordinateOrbits
    (pi : Q →* B) (r : ℕ) : Type where
  coordinate : Fin r →
    Fin (Module.finrank (ZMod 2) (Additive (binaryCentralOmega pi.ker)))
  separates : ∀ z : binaryCentralOmega pi.ker,
    (∀ i q, binaryOmegaCoordinate (coordinate i)
      (binaryKernelOmegaConjugateOmega pi q z) = 1) → z = 1

/-- A linear functional on the intrinsic omega module, regarded as a
multiplicative binary character.  Unlike `binaryOmegaCoordinate`, this
does not require the functional to be one of the canonical dual-basis
coordinates. -/
def binaryOmegaLinearFunctional
    {G : Type*} [Group G]
    (f : Module.Dual (ZMod 2) (Additive (binaryCentralOmega G))) :
    binaryCentralOmega G →* Multiplicative (ZMod 2) where
  toFun z := Multiplicative.ofAdd (f (Additive.ofMul z))
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, map_add]

@[simp] theorem binaryOmegaLinearFunctional_apply
    {G : Type*} [Group G]
    (f : Module.Dual (ZMod 2) (Additive (binaryCentralOmega G)))
    (z : binaryCentralOmega G) :
    (binaryOmegaLinearFunctional f z).toAdd = f (Additive.ofMul z) :=
  rfl

/-- The complex scalar character attached to an arbitrary binary linear
functional on central omega. -/
def binaryOmegaLinearScalarCharacter
    {G : Type*} [Group G]
    (f : Module.Dual (ZMod 2) (Additive (binaryCentralOmega G))) :
    binaryOmegaSubgroup G →* ℂ :=
  binaryScalarSign.comp
    ((binaryOmegaLinearFunctional f).comp
      binaryOmegaSubgroupEquiv.symm.toMonoidHom)

/-- Dual-functional form of the orbit certificate.  This is the natural
output of a module-generator argument: the chosen functionals may be
arbitrary linear combinations of the canonical omega coordinates. -/
structure BinaryKernelOmegaLinearOrbits
    (pi : Q →* B) (r : ℕ) : Type where
  functional : Fin r →
    Module.Dual (ZMod 2) (Additive (binaryCentralOmega pi.ker))
  separates : ∀ z : binaryCentralOmega pi.ker,
    (∀ i q, functional i
      (Additive.ofMul (binaryKernelOmegaConjugateOmega pi q z)) = 0) →
      z = 1

/-- Explicit dual-orbit span certificate.  The finite tuple records one
representative per slot and literal ambient translates of those
representatives.  Spanning the whole dual is a directly checkable linear
algebra condition and implies point separation on omega. -/
structure BinaryKernelOmegaDualOrbitSpan
    (pi : Q →* B) (r : ℕ) : Type where
  representative : Fin r →
    Module.Dual (ZMod 2) (Additive (binaryCentralOmega pi.ker))
  orbit : Fin r × Q →
    Module.Dual (ZMod 2) (Additive (binaryCentralOmega pi.ker))
  orbit_apply : ∀ i q z,
    orbit (i, q) (Additive.ofMul z) =
      representative i
        (Additive.ofMul (binaryKernelOmegaConjugateOmega pi q z))
  spans : Submodule.span (ZMod 2) (Set.range orbit) = ⊤

namespace BinaryKernelOmegaDualOrbitSpan

variable {pi : Q →* B} {r : ℕ}
  (C : BinaryKernelOmegaDualOrbitSpan pi r)

/-- A generating tuple for the dual of the actual omega conjugation
representation supplies the literal dual-orbit span certificate.  The
inverse in the contragredient action turns its evaluation back into
conjugation by the displayed ambient element. -/
noncomputable def ofDualGenerated
    (hgen : RepresentationGeneratedBy
      (binaryKernelOmegaConjugationRepresentation pi).dual r) :
    BinaryKernelOmegaDualOrbitSpan pi r := by
  let rho := binaryKernelOmegaConjugationRepresentation pi
  obtain ⟨representative, hspan⟩ :=
    orbit_span_eq_top_of_representationGeneratedBy rho.dual hgen
  let orbit : Fin r × Q →
      Module.Dual (ZMod 2) (Additive (binaryCentralOmega pi.ker)) :=
    fun iq ↦ rho.dual iq.2⁻¹ (representative iq.1)
  exact
    { representative := representative
      orbit := orbit
      orbit_apply := by
        intro i q z
        change representative i
            (rho ((q⁻¹)⁻¹) (Additive.ofMul z)) =
          representative i
            (Additive.ofMul (binaryKernelOmegaConjugateOmega pi q z))
        rw [inv_inv, binaryKernelOmegaConjugationRepresentation_apply]
      spans := by
        apply top_unique
        rw [← hspan]
        apply Submodule.span_mono
        rintro _ ⟨⟨i, q⟩, rfl⟩
        apply Submodule.subset_span
        exact ⟨(i, q⁻¹), by simp only [orbit, inv_inv]⟩ }

/-- A spanning tuple of ambient dual orbits separates every omega
element. -/
def toLinearOrbits : BinaryKernelOmegaLinearOrbits pi r where
  functional := C.representative
  separates := by
    intro z hz
    let evaluation :
        Module.Dual (ZMod 2) (Additive (binaryCentralOmega pi.ker)) →ₗ[ZMod 2]
          ZMod 2 :=
      { toFun := fun f ↦ f (Additive.ofMul z)
        map_add' := by intro f g; rfl
        map_smul' := by intro a f; rfl }
    have hevaluation : evaluation = 0 := by
      apply LinearMap.ext_on_range C.spans
      intro iq
      rcases iq with ⟨i, q⟩
      change C.orbit (i, q) (Additive.ofMul z) = 0
      rw [C.orbit_apply]
      exact hz i q
    have hall : ∀ f : Module.Dual (ZMod 2)
        (Additive (binaryCentralOmega pi.ker)),
        f (Additive.ofMul z) = 0 := by
      intro f
      have hf := LinearMap.congr_fun hevaluation f
      simpa only [evaluation, LinearMap.zero_apply] using hf
    have hz0 : Additive.ofMul z = 0 :=
      (Module.forall_dual_apply_eq_zero_iff
        (ZMod 2) (Additive.ofMul z)).mp hall
    apply Additive.ofMul.injective
    simpa only [ofMul_one] using hz0

end BinaryKernelOmegaDualOrbitSpan

namespace BinaryKernelOmegaLinearOrbits

variable {pi : Q →* B} {r : ℕ}
  (C : BinaryKernelOmegaLinearOrbits pi r)

/-- It is enough to generate the dual of an essential invariant
subrepresentation of omega.  Each chosen functional is extended to the
whole omega module.  If their ambient orbits vanished on a nonzero point,
they would vanish on its orbit span and hence on a nonzero point of the
essential subrepresentation, contradicting dual separation there.

This is the form used by the paired-eight socle argument: the detecting
subrepresentation is semisimple even when the whole omega module is not. -/
noncomputable def ofEssentialDualGenerated
    (S : Subrepresentation
      (binaryKernelOmegaConjugationRepresentation pi))
    (essential : ∀ x : Additive (binaryCentralOmega pi.ker), x ≠ 0 →
      ∃ y : S.toSubmodule, y ≠ 0 ∧
        (y : Additive (binaryCentralOmega pi.ker)) ∈
          binaryOrbitSpan
            (binaryKernelOmegaConjugationRepresentation pi) x)
    (hgen : RepresentationGeneratedBy S.toRepresentation.dual r) :
    BinaryKernelOmegaLinearOrbits pi r := by
  let rho := binaryKernelOmegaConjugationRepresentation pi
  obtain ⟨representative, hspan⟩ :=
    orbit_span_eq_top_of_representationGeneratedBy
      S.toRepresentation.dual hgen
  let functional : Fin r →
      Module.Dual (ZMod 2) (Additive (binaryCentralOmega pi.ker)) :=
    fun i ↦ S.toSubmodule.dualLift (representative i)
  exact
    { functional := functional
      separates := by
        intro z hz
        apply Additive.ofMul.injective
        change Additive.ofMul z = 0
        by_contra hz0
        obtain ⟨y, hy0, hyOrbit⟩ := essential (Additive.ofMul z) hz0
        have hvanish (i : Fin r) :
            ∀ x : Additive (binaryCentralOmega pi.ker),
              x ∈ binaryOrbitSpan rho (Additive.ofMul z) →
                functional i x = 0 := by
          intro x hx
          induction hx using Submodule.span_induction with
          | mem x hx =>
              obtain ⟨q, rfl⟩ := hx
              simpa only [rho,
                binaryKernelOmegaConjugationRepresentation_apply] using
                  hz i q
          | zero => simp only [map_zero]
          | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
          | smul a x _ hx => simp only [map_smul, hx, smul_zero]
        let evaluation : Module.Dual (ZMod 2) S.toSubmodule →ₗ[ZMod 2]
            ZMod 2 :=
          { toFun := fun f ↦ f y
            map_add' := by intro f g; rfl
            map_smul' := by intro a f; rfl }
        have hevaluation : evaluation = 0 := by
          apply LinearMap.ext_on_range hspan
          intro iq
          rcases iq with ⟨i, q⟩
          let yq : S.toSubmodule := S.toRepresentation q⁻¹ y
          have hyqOrbit :
              (yq : Additive (binaryCentralOmega pi.ker)) ∈
                binaryOrbitSpan rho (Additive.ofMul z) := by
            exact binaryOrbitSpan_apply_mem rho (Additive.ofMul z) q⁻¹
              hyOrbit
          have hv := hvanish i yq hyqOrbit
          change representative i yq = 0
          simpa only [functional, Submodule.dualLift_of_subtype] using hv
        have hall : ∀ f : Module.Dual (ZMod 2) S.toSubmodule, f y = 0 := by
          intro f
          have hf := LinearMap.congr_fun hevaluation f
          simpa only [evaluation, LinearMap.zero_apply] using hf
        have hyzero : y = 0 :=
          (Module.forall_dual_apply_eq_zero_iff (ZMod 2) y).mp hall
        exact hy0 hyzero }

/-- Canonical specialization to the sum of all minimal nonzero invariant
subspaces of omega.  Its essentiality is automatic for the finite omega
module, leaving only the dual generator theorem as semantic input. -/
noncomputable def ofSocleDualGenerated
    (hgen : RepresentationGeneratedBy
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.dual
      r) :
    BinaryKernelOmegaLinearOrbits pi r :=
  ofEssentialDualGenerated
    (finiteRepresentationSocle
      (binaryKernelOmegaConjugationRepresentation pi))
    (finiteRepresentationSocle_essential
      (binaryKernelOmegaConjugationRepresentation pi))
    hgen

/-- Schur-capacity endpoint for the canonical omega socle.  Once the
paired-eight three-layer argument bounds the capacity of its dual, the
standard semisimple generator theorem supplies the orbit tuple. -/
noncomputable def ofSocleDualSchurCapacity
    (hcap : representationSchurCapacity
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.dual ≤ r) :
    BinaryKernelOmegaLinearOrbits pi r := by
  let rho := binaryKernelOmegaConjugationRepresentation pi
  let S := finiteRepresentationSocle rho
  letI : IsSemisimpleModule (ZMod 2)[Q]
      S.toRepresentation.asModule :=
    finiteRepresentationSocle_isSemisimple rho
  letI : IsSemisimpleModule (ZMod 2)[Q]
      S.toRepresentation.dual.asModule :=
    representationDual_isSemisimple S.toRepresentation
  exact ofSocleDualGenerated
    (semisimple_representationGeneratedBy_of_schurCapacity_le
      S.toRepresentation.dual r hcap)

/-- Turn a generated tuple in the dual omega module into the literal
complex central characters used by the relative-kernel lift. -/
noncomputable def toOrbitCharacters :
    BinaryKernelOmegaOrbitCharacters pi r where
  character i := binaryOmegaLinearScalarCharacter (C.functional i)
  separates := by
    intro z hz
    apply C.separates z
    intro i q
    have h := hz i q
    have hsign : binaryOmegaLinearFunctional (C.functional i)
        (binaryKernelOmegaConjugateOmega pi q z) = 1 := by
      apply (binaryScalarSign_eq_one (k := ℂ) _).mp
      simpa only [binaryOmegaLinearScalarCharacter, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using h
    have hadd := congrArg Multiplicative.toAdd hsign
    simpa only [binaryOmegaLinearFunctional_apply,
      toAdd_one] using hadd

end BinaryKernelOmegaLinearOrbits

namespace BinaryKernelOmegaDualOrbitSpan

variable {pi : Q →* B} {r : ℕ}
  (C : BinaryKernelOmegaDualOrbitSpan pi r)

/-- Compose the checked dual-orbit span directly with the complex
orbit-character construction. -/
noncomputable def toOrbitCharacters :
    BinaryKernelOmegaOrbitCharacters pi r :=
  C.toLinearOrbits.toOrbitCharacters

end BinaryKernelOmegaDualOrbitSpan

namespace BinaryKernelOmegaCoordinateOrbits

variable {pi : Q →* B} {r : ℕ}
  (C : BinaryKernelOmegaCoordinateOrbits pi r)

/-- Taking every canonical omega coordinate always separates; this is the
fallback certificate before finite ambient orbits compress the tuple. -/
noncomputable def all
    (h : r = Module.finrank (ZMod 2)
      (Additive (binaryCentralOmega pi.ker))) :
    BinaryKernelOmegaCoordinateOrbits pi r where
  coordinate i := Fin.cast h i
  separates := by
    intro z hz
    apply binaryOmegaCoordinate_faithful z
    intro i
    let j : Fin r := Fin.cast h.symm i
    have hj := hz j 1
    simpa only [j, Fin.cast_cast, Fin.cast_eq_self,
      binaryKernelOmegaConjugateOmega_one] using hj

/-- A trivial prefix kernel needs no relative coordinate. -/
noncomputable def empty
    (pi : Q →* B) (hker : pi.ker = ⊥) :
    BinaryKernelOmegaCoordinateOrbits pi 0 where
  coordinate := Fin.elim0
  separates := by
    intro z _
    apply binaryCentralOmegaEmbedding_injective
    apply Subtype.ext
    have hz : ((binaryCentralOmegaEmbedding z : pi.ker) : Q) ∈ pi.ker :=
      (binaryCentralOmegaEmbedding z).property
    rw [hker, Subgroup.mem_bot] at hz
    exact hz

/-- Turn the checked coordinate-orbit certificate into literal complex
central characters. -/
noncomputable def toOrbitCharacters :
    BinaryKernelOmegaOrbitCharacters pi r where
  character i := binaryOmegaScalarCharacter (k := ℂ) (C.coordinate i)
  separates := by
    intro z hz
    apply C.separates z
    intro i q
    apply (binaryScalarSign_eq_one (k := ℂ) _).mp
    let omega := binaryKernelOmegaConjugateOmega pi q z
    have h := hz i q
    simpa only [binaryOmegaScalarCharacter, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, omega, MulEquiv.symm_apply_apply] using h

end BinaryKernelOmegaCoordinateOrbits

namespace BinaryKernelOmegaOrbitCharacters

variable {pi : Q →* B} {r : ℕ}
  (C : BinaryKernelOmegaOrbitCharacters pi r)

/-- Central characters give the kernel irreducibles consumed by the
overgroup lifting theorem. -/
noncomputable def toOrbitIrreducibles :
    BinaryKernelOmegaOrbitIrreducibles pi r := by
  have hexists (i : Fin r) :=
    exists_bundled_central_character
      (binaryOmegaSubgroup pi.ker) binaryOmegaSubgroup_central
      (C.character i)
  choose fibre scalar using hexists
  exact
    { fibre := fibre
      separates := by
        intro z hz
        apply C.separates z
        intro i q
        let omega := binaryKernelOmegaConjugateOmega pi q z
        let h : binaryOmegaSubgroup pi.ker := binaryOmegaSubgroupEquiv omega
        have hs (v : (fibre i).Space) := scalar i h v
        have ha : (fibre i).action (h : pi.ker) = 1 := by
          change (fibre i).action
            (binaryCentralOmegaEmbedding omega) = 1
          exact hz i q
        letI : Nontrivial (fibre i).action.asModule :=
          IsSimpleModule.nontrivial ℂ[pi.ker] (fibre i).action.asModule
        letI : Nontrivial (fibre i).Space :=
          (fibre i).action.asModuleEquiv.toEquiv.symm.nontrivial
        obtain ⟨v, hv⟩ := exists_ne (0 : (fibre i).Space)
        have hscalar : C.character i h = 1 :=
          (smul_left_injective ℂ hv) (by
            simpa only [ha, Module.End.one_apply, one_smul] using (hs v).symm)
        exact hscalar }

end BinaryKernelOmegaOrbitCharacters

namespace BinaryKernelOmegaOrbitIrreducibles

variable {pi : Q →* B} {r : ℕ}
  (C : BinaryKernelOmegaOrbitIrreducibles pi r)

/-- The irreducible whole-group representation lying over one displayed
kernel irreducible. -/
noncomputable def overgroup (i : Fin r) :
    OvergroupRestrictionConstituent (C.fibre i).action pi.ker.subtype :=
  OvergroupRestrictionConstituent.choose pi.ker (C.fibre i).action

/-- Bundle the lifted overgroup constituent in the character-count type. -/
noncomputable def relative (i : Fin r) :
    FiniteIrreducibleRepresentation ℂ Q where
  Space := (C.overgroup i).Space
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  action := (C.overgroup i).action
  irreducible := inferInstance

/-- The lifted whole-group irreducibles are jointly faithful when restricted
to the binary kernel. -/
theorem relative_faithful_on_kernel
    (hpi : IsPGroup 2 pi.ker) (x : pi.ker)
    (hx : ∀ i, (C.relative i).action (x : Q) = 1) :
    x = 1 := by
  apply binaryCentralOmega_joint_kernel_detection hpi
    (fun i ↦ (C.relative i).action.comp pi.ker.subtype)
  · intro z hz
    apply C.separates z
    intro i q
    let y := binaryKernelOmegaConjugate pi q z
    have hzq : (C.relative i).action (y : Q) = 1 := by
      change (C.relative i).action
        (q * (binaryCentralOmegaEmbedding z : Q) * q⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hz i]
      simp
    ext v
    apply (C.overgroup i).inclusion_injective
    have hintertwine :=
      Representation.IntertwiningMap.isIntertwining
        (C.fibre i).action
        ((C.relative i).action.comp pi.ker.subtype)
        (C.overgroup i).inclusion y v
    change (C.overgroup i).inclusion ((C.fibre i).action y v) =
      (C.overgroup i).inclusion v
    rw [hintertwine]
    change (C.relative i).action (y : Q) ((C.overgroup i).inclusion v) = _
    rw [hzq]
    rfl
  · exact hx

end BinaryKernelOmegaOrbitIrreducibles

namespace DegreeTwoPairRelativeKernelAnchor

/-- Build the complete relative-kernel anchor from a fixed prefix and a
normal-orbit tuple on the binary prefix kernel.  The relative representations
and their restriction constituents are constructed here; downstream finite
rows only have to supply the orbit-separation certificate. -/
noncomputable def ofBinaryKernelOmegaOrbitIrreducibles
    {profile : DegreeTwoPairRelativeProfile}
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    (orbit : BinaryKernelOmegaOrbitIrreducibles pi profile.relative) :
    DegreeTwoPairRelativeKernelAnchor Q profile where
  binary := binary
  binary_twoGroup := binary_twoGroup
  linear := linear
  ordinary := ordinary
  relative := orbit.relative
  kernel := pi.ker
  kernel_eq := kernel_eq
  kernel_twoGroup := kernel_twoGroup
  constituent := fun i ↦
    NormalRestrictionConstituent.choose (orbit.relative i).action pi.ker
  faithful := by
    intro q hbinary hlinear hord hrelative
    have hq : q ∈ pi.ker := by
      rw [kernel_eq]
      exact ⟨⟨fun i ↦ MonoidHom.mem_ker.mpr (hbinary i),
        fun i ↦ MonoidHom.mem_ker.mpr (hlinear i)⟩,
        fun i ↦ MonoidHom.mem_ker.mpr (hord i)⟩
    let x : pi.ker := ⟨q, hq⟩
    have hx : x = 1 := orbit.relative_faithful_on_kernel
      kernel_twoGroup x (fun i ↦ hrelative i)
    simpa using congrArg Subtype.val hx

/-- Character-facing form of
`ofBinaryKernelOmegaOrbitIrreducibles`.  A finite certificate may stay on
the intrinsic central omega subgroup; the required kernel irreducibles and
their ambient lifts are chosen uniformly. -/
noncomputable def ofBinaryKernelOmegaOrbitCharacters
    {profile : DegreeTwoPairRelativeProfile}
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    (orbit : BinaryKernelOmegaOrbitCharacters pi profile.relative) :
    DegreeTwoPairRelativeKernelAnchor Q profile :=
  ofBinaryKernelOmegaOrbitIrreducibles pi binary binary_twoGroup linear
    ordinary kernel_eq kernel_twoGroup orbit.toOrbitIrreducibles

end DegreeTwoPairRelativeKernelAnchor

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
