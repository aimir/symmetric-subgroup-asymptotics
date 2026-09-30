import SymmetricSubgroupAsymptotics.BinaryCarrierVaryingAxisRecovery

/-!
# Naturality of quotient-identity carrier cells

The unchanged cells in the carrier word use `quotientIdentitySlot`.  Their
quotient type varies with the exact normal axis, even when the displayed
action is fixed.  This file supplies the canonical comparison: an
automorphism of the displayed action which carries one axis to another acts
coordinatewise on the one-cell full carrier and descends to the corresponding
quotient equivalence.  Both legs of the carrier square commute exactly.

This is the identity-cell counterpart of
`BinaryCarrierTransportNaturality.carrierTransport_natural`.  In particular
it retains the actual quotient and does not replace it by an abstract group
of the same cardinality.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierIdentitySlotNaturality

open SymmetricSubgroupAsymptotics
open BinaryCarrierMenuSlots
open BinaryCarrierProfileTransport

variable (g : MixtureKind)

/-- Act on the one-cell full carrier by an automorphism of its displayed
original action. -/
def identityCarrierEquiv {h : MixtureKind}
    (e : mixtureAction g ≃* mixtureAction h) :
    identityCarrier g ≃* identityCarrier h where
  toFun x := ⟨fun i ↦ e (x.1 i),Subgroup.mem_top _⟩
  invFun x := ⟨fun i ↦ e.symm (x.1 i),Subgroup.mem_top _⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact e.symm_apply_apply (x.1 i)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact e.apply_symm_apply (x.1 i)
  map_mul' x y := by
    apply Subtype.ext
    funext i
    exact e.map_mul (x.1 i) (y.1 i)

@[simp] theorem identityCarrierEquiv_apply
    {h : MixtureKind} (e : mixtureAction g ≃* mixtureAction h)
    (x : identityCarrier g) (i : Fin 1) :
    (identityCarrierEquiv g e x).1 i = e (x.1 i) := rfl

/-- Embed an original action as the constant point of its one-cell full
carrier.  This is a multiplicative section of `identityCarrierEval`. -/
def identityCarrierSection :
    mixtureAction g →* identityCarrier g where
  toFun u := ⟨fun _ ↦ u,Subgroup.mem_top _⟩
  map_one' := by
    apply Subtype.ext
    funext i
    rfl
  map_mul' x y := by
    apply Subtype.ext
    funext i
    rfl

@[simp] theorem identityCarrierEval_section (u : mixtureAction g) :
    BinaryCarrierMenuSlots.identityCarrierEval g
        (identityCarrierSection g u) = u := rfl

@[simp] theorem identityCarrierEquiv_section
    {h : MixtureKind} (e : mixtureAction g ≃* mixtureAction h)
    (u : mixtureAction g) :
    identityCarrierEquiv g e (identityCarrierSection g u) =
      identityCarrierSection h (e u) := by
  rfl

@[simp] theorem identityCarrierEval_equiv
    {h : MixtureKind} (e : mixtureAction g ≃* mixtureAction h)
    (p : identityCarrier g) :
    BinaryCarrierMenuSlots.identityCarrierEval h
        (identityCarrierEquiv g e p) =
      e (BinaryCarrierMenuSlots.identityCarrierEval g p) := rfl

/-- Pulling the replacement kernel back along the constant section recovers
the source normal exactly. -/
theorem axis_eq_betaKer_comap_section
    (N : Subgroup (mixtureAction g)) [N.Normal] :
    N = (quotientIdentitySlot g N).beta.ker.comap
      (identityCarrierSection g) := by
  change N = (identityBeta g (QuotientGroup.mk' N)).ker.comap
    (identityCarrierSection g)
  rw [BinaryCarrierMenuSlots.identityBeta_ker_eq_comap]
  ext u
  change u ∈ N ↔
    BinaryCarrierMenuSlots.identityCarrierEval g
      (identityCarrierSection g u) ∈ (QuotientGroup.mk' N).ker
  rw [identityCarrierEval_section, QuotientGroup.ker_mk']

/-- Reverse identity-cell naturality.  If target recovery identifies the two
replacement kernels after the coordinate action equivalence, then that
equivalence carries the first source axis to the second.  This is the step
which permits constructing `QuotientGroup.congr` only after target equality
has exposed the retained annihilator/kernel. -/
theorem axis_map_eq_of_betaKer_map_eq
    {h : MixtureKind}
    (N : Subgroup (mixtureAction g)) (M : Subgroup (mixtureAction h))
    [N.Normal] [M.Normal]
    (e : mixtureAction g ≃* mixtureAction h)
    (hker :
      (quotientIdentitySlot g N).beta.ker.map
          (identityCarrierEquiv g e).toMonoidHom =
        (quotientIdentitySlot h M).beta.ker) :
    N.map e.toMonoidHom = M := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hsectionN : identityCarrierSection g x ∈
        (quotientIdentitySlot g N).beta.ker := by
      rw [axis_eq_betaKer_comap_section g N] at hx
      exact hx
    have hsectionM : identityCarrierSection h (e x) ∈
        (quotientIdentitySlot h M).beta.ker := by
      rw [← hker]
      exact Subgroup.mem_map.mpr
        ⟨identityCarrierSection g x,hsectionN,identityCarrierEquiv_section g e x⟩
    rw [axis_eq_betaKer_comap_section h M]
    exact hsectionM
  · intro hy
    have hsectionM : identityCarrierSection h y ∈
        (quotientIdentitySlot h M).beta.ker := by
      rw [axis_eq_betaKer_comap_section h M] at hy
      exact hy
    have hmapped : identityCarrierSection h y ∈
        (quotientIdentitySlot g N).beta.ker.map
          (identityCarrierEquiv g e).toMonoidHom := hker.symm ▸ hsectionM
    obtain ⟨p,hp,hpy⟩ := Subgroup.mem_map.mp hmapped
    let x := BinaryCarrierMenuSlots.identityCarrierEval g p
    have hx : x ∈ N := by
      rw [axis_eq_betaKer_comap_section g N]
      exact hp
    refine ⟨x,hx,?_⟩
    change e (BinaryCarrierMenuSlots.identityCarrierEval g p) = y
    calc
      e (BinaryCarrierMenuSlots.identityCarrierEval g p) =
          BinaryCarrierMenuSlots.identityCarrierEval h
            (identityCarrierEquiv g e p) :=
        (identityCarrierEval_equiv g e p).symm
      _ = BinaryCarrierMenuSlots.identityCarrierEval h
          (identityCarrierSection h y) := congrArg
            (BinaryCarrierMenuSlots.identityCarrierEval h) hpy
      _ = y := identityCarrierEval_section h y

variable {h : MixtureKind}
  (N : Subgroup (mixtureAction g)) (M : Subgroup (mixtureAction h))
  [N.Normal] [M.Normal]
  (e : mixtureAction g ≃* mixtureAction h)
  (haxis : N.map e.toMonoidHom = M)

/-- The quotient equivalence induced by an exact transported-axis equality. -/
abbrev quotientEquiv :
    (mixtureAction g ⧸ N) ≃* (mixtureAction h ⧸ M) :=
  QuotientGroup.congr N M e haxis

/-- The source quotient maps of the two identity slots commute with the
transported action equivalence. -/
theorem alpha_intertwine :
    (quotientEquiv g N M e haxis).toMonoidHom.comp
        (quotientIdentitySlot g N).alpha =
      (quotientIdentitySlot h M).alpha.comp e.toMonoidHom := by
  ext x
  rfl

/-- The replacement quotient maps commute with the coordinatewise action on
the one-cell full carrier. -/
theorem beta_intertwine :
    (quotientEquiv g N M e haxis).toMonoidHom.comp
        (quotientIdentitySlot g N).beta =
      (quotientIdentitySlot h M).beta.comp
        (identityCarrierEquiv g e).toMonoidHom := by
  ext x
  rfl

/-- Package the complete naturality square for later route-wise assembly. -/
theorem quotientIdentitySlot_natural :
    ((quotientEquiv g N M e haxis).toMonoidHom.comp
        (quotientIdentitySlot g N).alpha =
      (quotientIdentitySlot h M).alpha.comp e.toMonoidHom) ∧
    ((quotientEquiv g N M e haxis).toMonoidHom.comp
        (quotientIdentitySlot g N).beta =
      (quotientIdentitySlot h M).beta.comp
        (identityCarrierEquiv g e).toMonoidHom) :=
  ⟨alpha_intertwine g N M e haxis,beta_intertwine g N M e haxis⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierIdentitySlotNaturality

end
