import SymmetricSubgroupAsymptotics.InducedCoprimeHead
import SymmetricSubgroupAsymptotics.BinaryIrreducibleTuple
import Mathlib.RepresentationTheory.Maschke

/-!
# One irreducible constituent detects a normal restriction kernel

Let `K` be a normal subgroup of a finite group `Q`, and let `rho` be an
irreducible complex representation of `Q`.  Maschke supplies an irreducible
constituent of `rho|K`.  The `Q`-conjugates of any nonzero constituent span
the whole irreducible `Q`-module.  Consequently the kernel of `rho|K` is the
normal core of the kernel of that one constituent.

The pair-relative character count needs exactly this form.  After a fixed
prefix has identified the source preimage of a binary anchor kernel, one
Sylow-restricted constituent label determines the normal core, hence the
tail-character kernel, without charging every constituent separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {Q V : Type*} [Group Q] [Finite Q]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A chosen irreducible constituent of the restriction of `rho` to a
normal subgroup.  The inclusion is retained explicitly because downstream
kernel arguments compare the constituent with the original action. -/
structure NormalRestrictionConstituent
    (rho : Representation ℂ Q V) [Representation.IsIrreducible rho]
    (K : Subgroup Q) [K.Normal] : Type 1 where
  Space : Type
  addCommGroup : AddCommGroup Space
  module : Module ℂ Space
  finiteDimensional : FiniteDimensional ℂ Space
  action : Representation ℂ K Space
  irreducible : Representation.IsIrreducible action
  inclusion : action.IntertwiningMap (rho.comp K.subtype)
  inclusion_injective : Function.Injective inclusion

attribute [instance]
  NormalRestrictionConstituent.addCommGroup
  NormalRestrictionConstituent.module
  NormalRestrictionConstituent.finiteDimensional
  NormalRestrictionConstituent.irreducible

namespace NormalRestrictionConstituent

variable {rho : Representation ℂ Q V} [Representation.IsIrreducible rho]
  {K : Subgroup Q} [K.Normal]
  (C : NormalRestrictionConstituent rho K)

/-- The vectors fixed by every `Q`-conjugate of one element of `K` form a
`Q`-subrepresentation. -/
def conjugateFixedSubrepresentation (x : K) : Subrepresentation rho where
  toSubmodule :=
    { carrier := {v | ∀ q : Q,
          rho (q * (x : Q) * q⁻¹) v = v}
      zero_mem' := by intro q; simp
      add_mem' := by
        intro a b ha hb q
        rw [map_add, ha q, hb q]
      smul_mem' := by
        intro c v hv q
        rw [map_smul, hv q] }
  apply_mem_toSubmodule := by
    intro g v hv q
    have h := hv (g⁻¹ * q)
    change rho (q * (x : Q) * q⁻¹) (rho g v) = rho g v
    calc
      rho (q * (x : Q) * q⁻¹) (rho g v) =
          rho g (rho ((g⁻¹ * q) * (x : Q) * (g⁻¹ * q)⁻¹) v) := by
            simp only [map_mul, map_inv]
            group
      _ = rho g v := by rw [h]

/-- If the chosen constituent kills every conjugate of `x`, the original
irreducible representation kills `x`.  This is the kernel-core half of
Clifford theory needed by the relative-label argument; it is proved from
irreducibility and does not assume a prepackaged Clifford theorem. -/
theorem action_eq_one_of_conjugates_mem_constituent_kernel
    (x : K)
    (h : ∀ q : Q,
      C.action
        ⟨q * (x : Q) * q⁻¹,
          (show q * (x : Q) * q⁻¹ ∈ K from
            (inferInstance : K.Normal).conj_mem (x : Q) x.2 q)⟩ = 1) :
    rho (x : Q) = 1 := by
  let W := C.conjugateFixedSubrepresentation x
  have hC : ∀ v : C.Space, C.inclusion v ∈ W := by
    intro v q
    let y : K :=
      ⟨q * (x : Q) * q⁻¹,
        (show q * (x : Q) * q⁻¹ ∈ K from
          (inferInstance : K.Normal).conj_mem (x : Q) x.2 q)⟩
    have hintertwine := Representation.IntertwiningMap.isIntertwining
      C.action (rho.comp K.subtype) C.inclusion y v
    change rho (q * (x : Q) * q⁻¹) (C.inclusion v) = C.inclusion v
    change C.inclusion (C.action y v) =
      rho (q * (x : Q) * q⁻¹) (C.inclusion v) at hintertwine
    rw [h q, Module.End.one_apply] at hintertwine
    exact hintertwine.symm
  have hWne : W ≠ ⊥ := by
    letI : Nontrivial C.Space :=
      IsSimpleModule.nontrivial ℂ[K] C.action.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : C.Space)
    intro hbot
    have hvW : C.inclusion v ∈ W := hC v
    rw [hbot] at hvW
    have hz : C.inclusion v = 0 := by simpa using hvW
    exact hv (C.inclusion_injective (hz.trans C.inclusion.map_zero.symm))
  have hWtop : W = ⊤ := (eq_bot_or_eq_top W).resolve_left hWne
  ext v
  have hv : v ∈ W := by rw [hWtop]; exact Submodule.mem_top
  simpa only [W, conjugateFixedSubrepresentation, one_mul, inv_one,
    mul_one, Module.End.one_apply] using hv (1 : Q)

/-- Exact kernel-core formula for one chosen normal constituent. -/
theorem action_eq_one_iff_conjugates_mem_constituent_kernel
    (x : K) :
    rho (x : Q) = 1 ↔
      ∀ q : Q,
        C.action
          ⟨q * (x : Q) * q⁻¹,
            (show q * (x : Q) * q⁻¹ ∈ K from
              (inferInstance : K.Normal).conj_mem (x : Q) x.2 q)⟩ = 1 := by
  constructor
  · intro hx q
    apply C.inclusion_injective
    have hintertwine := Representation.IntertwiningMap.isIntertwining
      C.action (rho.comp K.subtype) C.inclusion
      ⟨q * (x : Q) * q⁻¹,
        (show q * (x : Q) * q⁻¹ ∈ K from
          (inferInstance : K.Normal).conj_mem (x : Q) x.2 q)⟩
    ext v
    change C.inclusion (C.action _ v) = C.inclusion v
    rw [hintertwine]
    change rho (q * (x : Q) * q⁻¹) (C.inclusion v) = C.inclusion v
    rw [map_mul, map_mul, map_inv, hx]
    simp
  · exact C.action_eq_one_of_conjugates_mem_constituent_kernel x

/-- Maschke gives a concrete chosen constituent for every restricted
irreducible complex representation. -/
noncomputable def choose
    (rho : Representation ℂ Q V) [Representation.IsIrreducible rho]
    (K : Subgroup Q) [K.Normal] :
    NormalRestrictionConstituent rho K := by
  letI : NeZero (Nat.card K : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos (α := K)).ne'⟩
  let restricted := rho.comp K.subtype
  letI : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial ℂ[Q] rho.asModule
  letI : Nontrivial V := rho.asModuleEquiv.toEquiv.symm.nontrivial
  letI : Nontrivial restricted.asModule :=
    restricted.asModuleEquiv.toEquiv.nontrivial
  letI : IsSemisimpleModule ℂ[K] restricted.asModule := inferInstance
  obtain ⟨S, hS⟩ :=
    IsSemisimpleModule.exists_simple_submodule ℂ[K] restricted.asModule
  let T : Subrepresentation restricted := Subrepresentation.ofSubmodule' S
  letI : IsSimpleModule ℂ[K] S := hS
  letI : AddCommGroup T.toSubmodule := inferInstance
  letI : AddCommGroup T.toRepresentation.asModule := inferInstance
  have hsimple : IsSimpleModule ℂ[K] T.toRepresentation.asModule :=
    (submoduleRepresentationModuleEquiv restricted S).toLinearMap
      |>.isSimpleModule_iff_of_bijective
        (submoduleRepresentationModuleEquiv restricted S).bijective
      |>.mp hS
  exact
    { Space := T.toSubmodule
      addCommGroup := inferInstance
      module := inferInstance
      finiteDimensional := inferInstance
      action := T.toRepresentation
      irreducible :=
        (Representation.irreducible_iff_isSimpleModule_asModule
          T.toRepresentation).mpr hsimple
      inclusion := subrepresentationInclusion restricted T
      inclusion_injective := T.toSubmodule.subtype_injective }

end NormalRestrictionConstituent

end SymmetricSubgroupAsymptotics

end
