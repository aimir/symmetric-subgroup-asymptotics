import SymmetricSubgroupAsymptotics.FusionCarrierAnnihilatorYonedaIncidence

/-!
# A nonabelian proper-subdirect regression fixture

The carrier is the whole symmetric group on three points with its sign
quotient, and the exterior source is the same group with the same sign map.
The literal pullback core `fusionCarrierSubdirectGraph` is then the
index-two subgroup of `S₃ × S₃` of pairs with equal sign.  It is nonabelian,
both of its projections are full, it is not the direct product of those
projections, and its first Goursat axis is the literal kernel of the sign.

One abelian layer takes the sign quotient to the trivial top, with the
kernel charted as the trivial `F₂`-module.  The retained flag of every
accepted epimorphism is read off its literal core, and the annihilator-aware
incidence applies to this carrier with the tower capacity.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace AnnihilatorYonedaFixture

/-- The sign character, with values in the permutations of two points. -/
def signPerm : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 2) where
  toFun g := if Equiv.Perm.sign g = 1 then 1 else Equiv.swap 0 1
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign h) with hh | hh <;>
      simp [hg, hh, Equiv.swap_mul_self]

theorem signPerm_swap : signPerm (Equiv.swap 0 1) = Equiv.swap 0 1 := by
  simp [signPerm, Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 1 by decide)]

theorem perm_two_cases : ∀ p : Equiv.Perm (Fin 2), p = 1 ∨ p = Equiv.swap 0 1 := by
  decide

theorem perm_two_comm : ∀ p p' : Equiv.Perm (Fin 2), p * p' = p' * p := by
  decide

/-- The sign quotient between the literal top subgroups. -/
def signTop : (⊤ : Subgroup (Equiv.Perm (Fin 3))) →*
    (⊤ : Subgroup (Equiv.Perm (Fin 2))) :=
  (Subgroup.topEquiv.symm.toMonoidHom).comp
    (signPerm.comp Subgroup.topEquiv.toMonoidHom)

@[simp] theorem signTop_apply (g : (⊤ : Subgroup (Equiv.Perm (Fin 3)))) :
    ((signTop g : (⊤ : Subgroup (Equiv.Perm (Fin 2)))) : Equiv.Perm (Fin 2)) =
      signPerm g := rfl

theorem signTop_surjective : Function.Surjective signTop := by
  intro y
  rcases perm_two_cases y.1 with hy | hy
  · refine ⟨1, Subtype.ext ?_⟩
    rw [hy, map_one]
    rfl
  · refine ⟨⟨Equiv.swap 0 1, Subgroup.mem_top _⟩, Subtype.ext ?_⟩
    rw [hy, signTop_apply]
    exact signPerm_swap

/-- The checked sign carrier on three points. -/
def signCarrier : CheckedPermutationCarrier 3 2 where
  source := ⊤
  carrier := ⊤
  quotient := ⊤
  axis := signTop.ker.map (⊤ : Subgroup (Equiv.Perm (Fin 3))).subtype
  carrierKernel := signTop.ker.map (⊤ : Subgroup (Equiv.Perm (Fin 3))).subtype
  alpha := signTop
  beta := signTop
  alpha_surjective := signTop_surjective
  beta_surjective := signTop_surjective
  alpha_kernel := rfl
  beta_kernel := rfl

/-- The complete exterior source: the whole symmetric group on three points. -/
abbrev source : Subgroup (Equiv.Perm (Fin 3)) := ⊤

/-- The sign epimorphism of the exterior source. -/
def signEpi : GroupEpimorphism source signCarrier.quotient :=
  ⟨signTop, signTop_surjective⟩

/-- The literal pullback core of the sign epimorphism. -/
abbrev core : Subgroup (signCarrier.carrier × source) :=
  fusionCarrierSubdirectGraph signCarrier source signEpi

theorem diagonal_mem_core (g : (⊤ : Subgroup (Equiv.Perm (Fin 3)))) :
    ((g, g) : signCarrier.carrier × source) ∈ core := by
  change signTop g = signTop g
  rfl

/-- The literal core is nonabelian. -/
theorem core_not_commutative : ¬ ∀ x y : core, x * y = y * x := by
  intro h
  let a : (⊤ : Subgroup (Equiv.Perm (Fin 3))) := ⟨Equiv.swap 0 1, Subgroup.mem_top _⟩
  let c : (⊤ : Subgroup (Equiv.Perm (Fin 3))) := ⟨Equiv.swap 1 2, Subgroup.mem_top _⟩
  have hac := congrArg (fun z : core => ((z.1.1 : (⊤ : Subgroup _)) :
    Equiv.Perm (Fin 3))) (h ⟨(a, a), diagonal_mem_core a⟩ ⟨(c, c), diagonal_mem_core c⟩)
  have hne : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠
      Equiv.swap 1 2 * Equiv.swap 0 1 := by
    decide
  exact hne hac

/-- The literal core is a proper subdirect product: both projections are
full, but an odd carrier element over the trivial source element is
missing, so it is not the direct product of its projections. -/
theorem core_proper_subdirect :
    Function.Surjective (Prod.fst ∘ core.subtype) ∧
      Function.Surjective (Prod.snd ∘ core.subtype) ∧
      core ≠ ⊤ := by
  refine ⟨fusionCarrierSubdirectGraph_fst_surjective signCarrier source signEpi,
    fusionCarrierSubdirectGraph_snd_surjective signCarrier source signEpi, ?_⟩
  intro htop
  let a : (⊤ : Subgroup (Equiv.Perm (Fin 3))) := ⟨Equiv.swap 0 1, Subgroup.mem_top _⟩
  have hmem : ((a, 1) : signCarrier.carrier × source) ∈ core := by
    rw [htop]
    exact Subgroup.mem_top _
  have hval := congrArg Subtype.val (show signTop a = signTop 1 from hmem)
  rw [signTop_apply, map_one] at hval
  have hswap : (Equiv.swap (0 : Fin 2) 1) ≠ 1 := by decide
  exact hswap (signPerm_swap.symm.trans hval)

/-- The first Goursat axis of the literal core is the literal sign kernel. -/
theorem core_axis : core.goursatFst = signTop.ker :=
  fusionCarrierSubdirectGraph_axis signCarrier source signEpi

/-! ### One abelian layer to the trivial top -/

/-- The carrier quotient. -/
abbrev Q : Type := signCarrier.quotient

theorem Q_card : Nat.card Q = 2 := by
  change Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 2))) = 2
  rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]
  rfl

/-- The trivial comparator top. -/
abbrev T : Type := Q ⧸ (⊤ : Subgroup Q)

/-- The kernel module of the single layer. -/
abbrev layerModule : Rep (ZMod 2) T := Rep.trivial (ZMod 2) T (ZMod 2)

instance layerModule_finite : Finite layerModule :=
  inferInstanceAs (Finite (ZMod 2))

/-- The literal kernel of the layer, charted as the trivial `F₂`-module. -/
def layerChart : OriginalKernelModuleChart (QuotientGroup.mk' (⊤ : Subgroup Q))
    layerModule where
  equiv :=
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    (mulEquivOfPrimeCardEq (G := Multiplicative (ZMod 2)) (G' := Q)
      (by rw [Nat.card_eq_fintype_card]; rfl) Q_card).trans
      (Subgroup.topEquiv.symm.trans
        (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (⊤ : Subgroup Q)).symm))
  conjugate := by
    intro q a
    rw [Rep.trivial_ρ_apply]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      perm_two_comm q.1, mul_inv_cancel_right]

/-- The one-layer abelian tower from the sign quotient to the trivial top. -/
def signTower : AbelianYonedaTower T Q
    ((MonoidHom.id T).comp (QuotientGroup.mk' (⊤ : Subgroup Q))) :=
  .layer (QuotientGroup.mk' (⊤ : Subgroup Q))
    (QuotientGroup.mk'_surjective _) (ZMod 2) layerModule layerChart .base

/-- The accepted family used by the fixture: every sign-carrier epimorphism. -/
abbrev Accepted : Subgroup (signCarrier.carrier × Equiv.Perm (Fin 3)) → Prop :=
  fun _ => True

/-- Every retained layer datum is read off the literal pullback core. -/
theorem flag_from_core
    (γ : FusionCarrierAcceptedEpi signCarrier source Accepted) :
    fusionCarrierCoreFlag signCarrier source Accepted
        (fun δ => signTower.flag source δ.1.1)
        (fusionCarrierSubdirectGraph signCarrier source γ.1) =
      some (signTower.flag source γ.1.1) :=
  fusionCarrierCoreFlag_core signCarrier source Accepted
    (fun δ => signTower.flag source δ.1.1) γ

/-- The bottom map of the layer is the literal core's carrier coordinate
pushed to the layer target. -/
theorem layer_bottom_from_core
    (x : signCarrier.carrier × source) (hx : x ∈ core) :
    QuotientGroup.mk' (⊤ : Subgroup Q) (signEpi.1 x.2) =
      QuotientGroup.mk' (⊤ : Subgroup Q) (signCarrier.beta x.1) := by
  rw [show signCarrier.beta x.1 = signEpi.1 x.2 from hx]

/-- The annihilator-aware incidence on the sign carrier. -/
theorem sign_incidence :
    (Nat.card (FusionCarrierAcceptedEpi signCarrier source Accepted) : ℝ) ≤
      (signTower.capacity source : ℝ) * completeQuotientWeight (R := Q) source :=
  fusionCarrierAcceptedEpi_card_le_abelianTower signCarrier source Accepted
    (⊤ : Subgroup Q) signTower

end AnnihilatorYonedaFixture
end SymmetricSubgroupAsymptotics

end
