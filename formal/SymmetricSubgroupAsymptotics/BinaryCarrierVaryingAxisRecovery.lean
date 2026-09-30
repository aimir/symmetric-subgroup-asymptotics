import SymmetricSubgroupAsymptotics.BinaryCarrierMenuSlots

/-!
# Recovery of varying axes from transported carriers

The simultaneous carrier transport remembers more than the common quotient
relation.  When the source relation has its displayed quotient kernels as its
exact coordinate axes, the transported relation has the replacement quotient
kernels as its exact coordinate axes.  This is valid for arbitrary groups.

For an identity slot the replacement kernel is the pullback of the original
normal subgroup along the one-coordinate evaluation map.  That evaluation is
surjective, so this pullback is injective as a function of the original normal
subgroup.  Thus an unchanged quotient-identity coordinate has fibre one even
when its axis varies.  The ambient corollary keeps every replacement carrier
literal; in particular it applies to nonabelian proper subdirect carriers.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-! ## Exact axes under simultaneous transport -/

variable {ι : Type*} {U P Q : ι → Type*}
  [∀ i, Group (U i)] [∀ i, Group (P i)] [∀ i, Group (Q i)]

/-- Exact coordinate axes pass through the simultaneous quotient transport.
No commutativity or fullness hypothesis is used. -/
theorem carrierAxis_carrierTransport_eq_ker [Finite ι] [DecidableEq ι]
    (α : ∀ i, U i →* Q i) (β : ∀ i, P i →* Q i)
    (H : Subgroup (∀ i, U i))
    (haxis : ∀ i, carrierAxis H i = (α i).ker) (i : ι) :
    carrierAxis (carrierTransport α β H) i = (β i).ker := by
  ext p
  constructor
  · intro hp
    change carrierProductMap β (MonoidHom.mulSingle P i p) ∈
      H.map (carrierProductMap α) at hp
    obtain ⟨u,huH,hu⟩ := Subgroup.mem_map.mp hp
    have huoff : ∀ j, j ≠ i → u j ∈ (α j).ker := by
      intro j hji
      change α j (u j) = 1
      have hj := congrFun hu j
      simpa [carrierProductMap,hji] using hj
    let uoff : ∀ j, U j := Function.update u i 1
    have huoffH : uoff ∈ H := by
      apply Subgroup.pi_mem_of_mulSingle_mem
      intro j
      change uoff j ∈ carrierAxis H j
      rw [haxis j]
      by_cases hji : j = i
      · subst j
        simp [uoff]
      · simpa [uoff,hji] using huoff j hji
    have hui : u i ∈ carrierAxis H i := by
      change MonoidHom.mulSingle U i (u i) ∈ H
      have hm := H.mul_mem huH (H.inv_mem huoffH)
      convert hm using 1
      funext j
      by_cases hji : j = i
      · subst j
        simp [uoff]
      · simp [uoff,hji]
    change β i p = 1
    have hai : α i (u i) = 1 := by
      change u i ∈ (α i).ker
      rw [← haxis i]
      exact hui
    have hi := congrFun hu i
    calc
      β i p = α i (u i) := by
        simpa [carrierProductMap] using hi.symm
      _ = 1 := hai
  · intro hp
    change carrierProductMap β (MonoidHom.mulSingle P i p) ∈
      H.map (carrierProductMap α)
    have hmap : carrierProductMap β (MonoidHom.mulSingle P i p) = 1 := by
      funext j
      by_cases hji : j = i
      · subst j
        simpa [carrierProductMap] using hp
      · simp [carrierProductMap,hji]
    rw [hmap]
    exact (H.map (carrierProductMap α)).one_mem

section DisplayedCarriers

variable {κ : ι → Type*} {V : ∀ i, κ i → Type*}
  [∀ i j, Group (V i j)]

/-- Pulling the ambient transported subgroup back to its literal retained
carriers exposes the exact replacement axes.  Since `C i` is never replaced
by the product of its projections, this includes proper nonabelian subdirect
carriers. -/
theorem carrierAxis_carrierTransportInAmbient_comap_eq_ker
    [Finite ι] [DecidableEq ι]
    (C : ∀ i, Subgroup (∀ j, V i j))
    (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
    (H : Subgroup (∀ i, U i))
    (haxis : ∀ i, carrierAxis H i = (α i).ker) (i : ι) :
    carrierAxis
      ((carrierTransportInAmbient C α β H).comap
        (carrierReplacementEmbedding C)) i = (β i).ker := by
  unfold carrierTransportInAmbient
  rw [Subgroup.comap_map_eq_self_of_injective
    (carrierReplacementEmbedding_injective C)]
  exact carrierAxis_carrierTransport_eq_ker α β H haxis i

/-- Equality of two ambient transported subgroups recovers equality of every
replacement kernel, even when the two common-quotient families have different
types.  This is the form needed to compare decorated cells whose axes vary.
The retained carriers `C i` remain literal throughout. -/
theorem carrierReplacement_kernels_eq_of_ambientTransport_eq
    [Finite ι] [DecidableEq ι]
    {Q₁ Q₂ : ι → Type*} [∀ i, Group (Q₁ i)] [∀ i, Group (Q₂ i)]
    (C : ∀ i, Subgroup (∀ j, V i j))
    (α₁ : ∀ i, U i →* Q₁ i) (β₁ : ∀ i, C i →* Q₁ i)
    (α₂ : ∀ i, U i →* Q₂ i) (β₂ : ∀ i, C i →* Q₂ i)
    (H₁ H₂ : Subgroup (∀ i, U i))
    (haxis₁ : ∀ i, carrierAxis H₁ i = (α₁ i).ker)
    (haxis₂ : ∀ i, carrierAxis H₂ i = (α₂ i).ker)
    (htransport :
      carrierTransportInAmbient C α₁ β₁ H₁ =
        carrierTransportInAmbient C α₂ β₂ H₂) :
    ∀ i, (β₁ i).ker = (β₂ i).ker := by
  intro i
  calc
    (β₁ i).ker =
        carrierAxis
          ((carrierTransportInAmbient C α₁ β₁ H₁).comap
            (carrierReplacementEmbedding C)) i :=
      (carrierAxis_carrierTransportInAmbient_comap_eq_ker
        C α₁ β₁ H₁ haxis₁ i).symm
    _ = carrierAxis
          ((carrierTransportInAmbient C α₂ β₂ H₂).comap
            (carrierReplacementEmbedding C)) i :=
      congrArg
        (fun T : Subgroup (∀ i j, V i j) =>
          carrierAxis (T.comap (carrierReplacementEmbedding C)) i)
        htransport
    _ = (β₂ i).ker :=
      carrierAxis_carrierTransportInAmbient_comap_eq_ker
        C α₂ β₂ H₂ haxis₂ i

end DisplayedCarriers

/-! ## Fibre-one recovery for a varying identity axis -/

namespace BinaryCarrierMenuSlots

open BinaryCarrierProfileTransport BinaryCarrierWordClosure

variable (g : MixtureKind)

/-- Evaluation of the literal one-cell identity carrier at its unique cell. -/
def identityCarrierEval : identityCarrier g →* mixtureAction g :=
  (MulEquiv.piUnique (fun _ : Fin 1 => mixtureAction g)).toMonoidHom.comp
    (identityCarrier g).subtype

theorem identityCarrierEval_surjective :
    Function.Surjective (identityCarrierEval g) := by
  intro u
  exact ⟨⟨fun _ => u,Subgroup.mem_top _⟩,rfl⟩

/-- The kernel written into an identity replacement is exactly the pullback
of the varying source axis. -/
theorem identityBeta_ker_eq_comap {Q : Type*} [Group Q]
    (α : mixtureAction g →* Q) :
    (identityBeta g α).ker = (α.ker).comap (identityCarrierEval g) := by
  ext p
  rfl

/-- In a one-coordinate simultaneous transport, the target `carrierAxis`
itself is the pullback of the source axis.  This is the direct recovery lemma
used for an unchanged coordinate in a mixed carrier word. -/
theorem carrierAxis_single_identityTransport_eq_comap
    {Q : Type*} [Group Q] (α : mixtureAction g →* Q)
    (H : Subgroup (∀ _ : Fin 1, mixtureAction g))
    (haxis : carrierAxis H 0 = α.ker) :
    carrierAxis
      (carrierTransport (fun _ : Fin 1 => α)
        (fun _ : Fin 1 => identityBeta g α) H) 0 =
      α.ker.comap (identityCarrierEval g) := by
  have hall : ∀ i : Fin 1, carrierAxis H i = α.ker := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact haxis
  calc
    carrierAxis
        (carrierTransport (fun _ : Fin 1 => α)
          (fun _ : Fin 1 => identityBeta g α) H) 0 =
        (identityBeta g α).ker :=
      carrierAxis_carrierTransport_eq_ker
        (fun _ : Fin 1 => α) (fun _ : Fin 1 => identityBeta g α) H hall 0
    _ = α.ker.comap (identityCarrierEval g) :=
      identityBeta_ker_eq_comap g α

/-- For the quotient attached to a normal axis `N`, the target axis retains
`N` literally through the one-coordinate chart. -/
theorem quotientIdentitySlot_beta_ker_eq_comap
    (N : Subgroup (mixtureAction g)) [N.Normal] :
    (quotientIdentitySlot g N).beta.ker =
      N.comap (identityCarrierEval g) := by
  change (identityBeta g (QuotientGroup.mk' N)).ker =
    N.comap (identityCarrierEval g)
  rw [identityBeta_ker_eq_comap,QuotientGroup.ker_mk']

/-- Hence the target identity axis determines the varying normal subgroup
with fibre one. -/
theorem identityAxis_pullback_injective :
    Function.Injective
      (fun N : Subgroup (mixtureAction g) =>
        N.comap (identityCarrierEval g)) :=
  Subgroup.comap_injective (identityCarrierEval_surjective g)

/-- Cross-cell form of fibre-one recovery.  The two quotient types may be
different: equality is asked only of the transported subgroups in the common
literal identity carrier.  Their target coordinate axes then recover the two
normal subgroups and force them to agree. -/
theorem quotientIdentity_axis_eq_of_single_transport_eq
    (N M : Subgroup (mixtureAction g)) [N.Normal] [M.Normal]
    (HN HM : Subgroup (∀ _ : Fin 1, mixtureAction g))
    (hN : carrierAxis HN 0 = N) (hM : carrierAxis HM 0 = M)
    (htransport :
      carrierTransport
          (fun _ : Fin 1 => QuotientGroup.mk' N)
          (fun _ : Fin 1 => identityBeta g (QuotientGroup.mk' N)) HN =
        carrierTransport
          (fun _ : Fin 1 => QuotientGroup.mk' M)
          (fun _ : Fin 1 => identityBeta g (QuotientGroup.mk' M)) HM) :
    N = M := by
  have hsN : carrierAxis HN 0 = (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact hN
  have hsM : carrierAxis HM 0 = (QuotientGroup.mk' M).ker := by
    rw [QuotientGroup.ker_mk']
    exact hM
  have htN :
      carrierAxis
          (carrierTransport
            (fun _ : Fin 1 => QuotientGroup.mk' N)
            (fun _ : Fin 1 => identityBeta g (QuotientGroup.mk' N)) HN) 0 =
        N.comap (identityCarrierEval g) := by
    rw [carrierAxis_single_identityTransport_eq_comap g
      (QuotientGroup.mk' N) HN hsN,QuotientGroup.ker_mk']
  have htM :
      carrierAxis
          (carrierTransport
            (fun _ : Fin 1 => QuotientGroup.mk' M)
            (fun _ : Fin 1 => identityBeta g (QuotientGroup.mk' M)) HM) 0 =
        M.comap (identityCarrierEval g) := by
    rw [carrierAxis_single_identityTransport_eq_comap g
      (QuotientGroup.mk' M) HM hsM,QuotientGroup.ker_mk']
  apply identityAxis_pullback_injective g
  calc
    N.comap (identityCarrierEval g) =
        carrierAxis
          (carrierTransport
            (fun _ : Fin 1 => QuotientGroup.mk' N)
            (fun _ : Fin 1 => identityBeta g (QuotientGroup.mk' N)) HN) 0 :=
      htN.symm
    _ = carrierAxis
          (carrierTransport
            (fun _ : Fin 1 => QuotientGroup.mk' M)
            (fun _ : Fin 1 => identityBeta g (QuotientGroup.mk' M)) HM) 0 :=
      congrArg (fun T => carrierAxis T 0) htransport
    _ = M.comap (identityCarrierEval g) := htM

end BinaryCarrierMenuSlots

end SymmetricSubgroupAsymptotics
