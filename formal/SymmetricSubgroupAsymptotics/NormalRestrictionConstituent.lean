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
open CategoryTheory

namespace SymmetricSubgroupAsymptotics

variable {Q V : Type} [Group Q] [Finite Q]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- An irreducible representation of an overgroup together with an
explicit copy of a prescribed irreducible subgroup representation in its
restriction.  This is the small piece of Frobenius reciprocity needed by
the relative binary-kernel construction. -/
structure OvergroupRestrictionConstituent
    {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W]
    (tau : Representation ℂ H W) [Representation.IsIrreducible tau]
    {Q : Type} [Group Q] (phi : H →* Q) : Type 1 where
  Space : Type
  addCommGroup : AddCommGroup Space
  module : Module ℂ Space
  finiteDimensional : FiniteDimensional ℂ Space
  action : Representation ℂ Q Space
  irreducible : Representation.IsIrreducible action
  inclusion : tau.IntertwiningMap (action.comp phi)
  inclusion_injective : Function.Injective inclusion

attribute [instance]
  OvergroupRestrictionConstituent.addCommGroup
  OvergroupRestrictionConstituent.module
  OvergroupRestrictionConstituent.finiteDimensional
  OvergroupRestrictionConstituent.irreducible

namespace OvergroupRestrictionConstituent

variable {W : Type} [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ W]

/-- Frobenius reciprocity and Maschke produce an irreducible overgroup
constituent whose restriction contains the prescribed subgroup
irreducible.  The proof chooses a simple summand of the induced module,
splits its inclusion, and applies the induction--restriction adjunction to
the resulting nonzero projection. -/
noncomputable def choose
    {Q : Type} [Group Q] [Finite Q]
    (H : Subgroup Q)
    (tau : Representation ℂ H W) [Representation.IsIrreducible tau] :
    OvergroupRestrictionConstituent tau H.subtype := by
  let I := Representation.ind H.subtype tau
  letI : FiniteDimensional ℂ (Representation.IndV H.subtype tau) :=
    induced_finiteDimensional H tau
  letI : Nontrivial tau.asModule :=
    IsSimpleModule.nontrivial ℂ[H] tau.asModule
  letI : Nontrivial W := tau.asModuleEquiv.toEquiv.symm.nontrivial
  have hmk : Function.Injective
      (Representation.IndV.mk H.subtype tau (1 : Q)) := by
    intro x y hxy
    have hmap := congrArg
      (fun z : Representation.IndV H.subtype tau ↦
        (((Rep.indToCoind (Rep.of tau)) z :
          Representation.coindV H.subtype tau) : Q → W) (1 : Q)) hxy
    simp [Rep.indToCoind, Rep.indToCoindAux,
      Representation.IndV.mk] at hmap
    change tau (⟨1, by simp⟩ : H) x = tau (⟨1, by simp⟩ : H) y at hmap
    simpa only [show (⟨1, by simp⟩ : H) = 1 by ext; simp,
      map_one, Module.End.one_apply] using hmap
  letI : Nontrivial (Representation.IndV H.subtype tau) := hmk.nontrivial
  letI : Nontrivial I.asModule := I.asModuleEquiv.toEquiv.nontrivial
  letI : NeZero (Nat.card Q : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos (α := Q)).ne'⟩
  letI : IsSemisimpleModule ℂ[Q] I.asModule := inferInstance
  let S := Classical.choose
    (IsSemisimpleModule.exists_simple_submodule ℂ[Q] I.asModule)
  have hS : IsSimpleModule ℂ[Q] S := Classical.choose_spec
    (IsSemisimpleModule.exists_simple_submodule ℂ[Q] I.asModule)
  let T : Subrepresentation I := Subrepresentation.ofSubmodule' S
  letI : IsSimpleModule ℂ[Q] S := hS
  letI : AddCommGroup T.toSubmodule := inferInstance
  letI : AddCommGroup T.toRepresentation.asModule := inferInstance
  have hsimple : IsSimpleModule ℂ[Q] T.toRepresentation.asModule :=
    (submoduleRepresentationModuleEquiv I S).toLinearMap
      |>.isSimpleModule_iff_of_bijective
        (submoduleRepresentationModuleEquiv I S).bijective
      |>.mp hS
  let f : T.toRepresentation.asModule →ₗ[ℂ[Q]] I.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      T.toRepresentation I (subrepresentationInclusion I T)
  have hf : Function.Injective f := Subtype.val_injective
  let idT : T.toRepresentation.asModule →ₗ[ℂ[Q]]
      T.toRepresentation.asModule := LinearMap.id
  let p := Classical.choose (IsSemisimpleModule.extension_property f hf idT)
  have hp : p.comp f = idT :=
    Classical.choose_spec (IsSemisimpleModule.extension_property f hf idT)
  let pRep : I.IntertwiningMap T.toRepresentation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      I T.toRepresentation).symm p
  have hpRep_ne : pRep ≠ 0 := by
    intro hpRep
    have hp0 : p = 0 := by
      calc
        p = (Representation.IntertwiningMap.equivLinearMapAsModule
            I T.toRepresentation) pRep := by
              exact (Representation.IntertwiningMap.equivLinearMapAsModule
                I T.toRepresentation).apply_symm_apply p |>.symm
        _ = (Representation.IntertwiningMap.equivLinearMapAsModule
            I T.toRepresentation) 0 := congrArg _ hpRep
        _ = 0 := map_zero _
    letI : Nontrivial T.toRepresentation.asModule :=
      IsSimpleModule.nontrivial ℂ[Q] T.toRepresentation.asModule
    obtain ⟨x, hx⟩ := exists_ne (0 : T.toRepresentation.asModule)
    have happ := LinearMap.congr_fun hp x
    rw [hp0] at happ
    exact hx (by simpa only [idT, LinearMap.zero_comp,
      LinearMap.zero_apply, LinearMap.id_coe, id_eq] using happ.symm)
  let inclusion : tau.IntertwiningMap
      (T.toRepresentation.comp H.subtype) :=
    inducedHomRestrictionEquiv H tau T.toRepresentation pRep
  have hinclusion_ne : inclusion ≠ 0 := by
    intro hz
    apply hpRep_ne
    apply (inducedHomRestrictionEquiv H tau T.toRepresentation).injective
    exact hz
  have hinclusion : Function.Injective inclusion :=
    (Representation.IsIrreducible.injective_or_eq_zero inclusion).resolve_right
      hinclusion_ne
  exact
    { Space := T.toSubmodule
      addCommGroup := inferInstance
      module := inferInstance
      finiteDimensional := inferInstance
      action := T.toRepresentation
      irreducible :=
        (Representation.irreducible_iff_isSimpleModule_asModule
          T.toRepresentation).mpr hsimple
      inclusion := inclusion
      inclusion_injective := hinclusion }

end OvergroupRestrictionConstituent

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
            have heq :
                (q * (x : Q) * q⁻¹) * g =
                  g * ((g⁻¹ * q) * (x : Q) * (g⁻¹ * q)⁻¹) := by
              group
            simpa only [map_mul, Module.End.mul_apply] using
              congrArg (fun h : Q ↦ rho h v) heq
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
  let W := conjugateFixedSubrepresentation (rho := rho) x
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
    ext v
    apply C.inclusion_injective
    have hintertwine := Representation.IntertwiningMap.isIntertwining
      C.action (rho.comp K.subtype) C.inclusion
      ⟨q * (x : Q) * q⁻¹,
        (show q * (x : Q) * q⁻¹ ∈ K from
          (inferInstance : K.Normal).conj_mem (x : Q) x.2 q)⟩
    change C.inclusion (C.action _ v) = C.inclusion v
    rw [hintertwine]
    change rho (q * (x : Q) * q⁻¹) (C.inclusion v) = C.inclusion v
    have hconj : rho (q * (x : Q) * q⁻¹) = 1 := by
      calc
        rho (q * (x : Q) * q⁻¹) =
            rho q * rho (x : Q) * rho q⁻¹ := by rw [map_mul, map_mul]
        _ = rho q * 1 * rho q⁻¹ := by rw [hx]
        _ = rho (q * q⁻¹) := by
          simpa only [mul_one] using (map_mul rho q q⁻¹).symm
        _ = 1 := by simp
    rw [hconj, Module.End.one_apply]
  · exact C.action_eq_one_of_conjugates_mem_constituent_kernel x

/-- Maschke gives a concrete chosen constituent for every restricted
irreducible complex representation. -/
noncomputable def choose
    (rho : Representation ℂ Q V) [Representation.IsIrreducible rho]
    (K : Subgroup Q) [K.Normal] :
    NormalRestrictionConstituent rho K := by
  letI : NeZero (Nat.card K : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos (α := K)).ne'⟩
  let restricted : Representation ℂ K V := rho.comp K.subtype
  letI : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial ℂ[Q] rho.asModule
  letI : Nontrivial V := rho.asModuleEquiv.toEquiv.symm.nontrivial
  letI : Nontrivial restricted.asModule :=
    restricted.asModuleEquiv.toEquiv.nontrivial
  letI : IsSemisimpleModule ℂ[K] restricted.asModule := inferInstance
  let S := Classical.choose
    (IsSemisimpleModule.exists_simple_submodule ℂ[K] restricted.asModule)
  have hS : IsSimpleModule ℂ[K] S := Classical.choose_spec
    (IsSemisimpleModule.exists_simple_submodule ℂ[K] restricted.asModule)
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
