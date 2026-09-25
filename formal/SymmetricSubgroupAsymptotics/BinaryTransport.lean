import SymmetricSubgroupAsymptotics.BinaryFamilies
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Reversible transport through original proper subdirect carriers

The replacement groups remain literal subgroups of their displayed products.
All original axes and common quotient maps are retained. No commutativity of
the source, the common quotient, or the replacement groups is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : Type*} {U P Q : ι → Type*}
  [∀ i, Group (U i)] [∀ i, Group (P i)] [∀ i, Group (Q i)]

/-- Fullness on every original coordinate, allowing arbitrary correlations. -/
def CarrierProductFull (H : Subgroup (∀ i, U i)) : Prop :=
  ∀ i (u : U i), ∃ h : H, h.1 i = u

/-- The literal embedded coordinate axis of the actual source subgroup. -/
def carrierAxis [DecidableEq ι] (H : Subgroup (∀ i, U i)) (i : ι) : Subgroup (U i) :=
  H.comap (MonoidHom.mulSingle U i)

/-- The simultaneous product of the original quotient maps. -/
def carrierProductMap (α : ∀ i, U i →* Q i) : (∀ i, U i) →* (∀ i, Q i) where
  toFun u i := α i (u i)
  map_one' := by funext i; exact map_one (α i)
  map_mul' u v := by funext i; exact map_mul (α i) (u i) (v i)

theorem carrierProductMap_surjective (α : ∀ i, U i →* Q i)
    (hα : ∀ i, Function.Surjective (α i)) : Function.Surjective (carrierProductMap α) := by
  intro q
  choose u hu using fun i => hα i (q i)
  exact ⟨u,funext hu⟩

/-- Finite independent coordinate axes generate the full product kernel.
This uses commuting disjoint supports, not abelian coordinate groups. -/
theorem carrierProductMap_ker_le_of_axes [Finite ι] [DecidableEq ι]
    (α : ∀ i, U i →* Q i) (H : Subgroup (∀ i, U i))
    (haxis : ∀ i, (α i).ker ≤ carrierAxis H i) :
    (carrierProductMap α).ker ≤ H := by
  intro u hu
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro i
  apply haxis i
  exact congrFun hu i

/-- The actual simultaneous full preimage in the entire proper replacement
group. No replacement group is enlarged to the product of its projections. -/
def carrierTransport (α : ∀ i, U i →* Q i) (β : ∀ i, P i →* Q i)
    (H : Subgroup (∀ i, U i)) : Subgroup (∀ i, P i) :=
  (H.map (carrierProductMap α)).comap (carrierProductMap β)

/-- The complete joint quotient relation survives the transport exactly. -/
theorem carrierTransport_quotient (α : ∀ i, U i →* Q i) (β : ∀ i, P i →* Q i)
    (hβ : ∀ i, Function.Surjective (β i)) (H : Subgroup (∀ i, U i)) :
    (carrierTransport α β H).map (carrierProductMap β) = H.map (carrierProductMap α) :=
  Subgroup.map_comap_eq_self_of_surjective (carrierProductMap_surjective β hβ) _

/-- Reconstruct the literal original subgroup from the whole new relation. -/
theorem carrierTransport_reconstruct [Finite ι] [DecidableEq ι]
    (α : ∀ i, U i →* Q i) (β : ∀ i, P i →* Q i)
    (hβ : ∀ i, Function.Surjective (β i)) (H : Subgroup (∀ i, U i))
    (haxis : ∀ i, (α i).ker ≤ carrierAxis H i) :
    ((carrierTransport α β H).map (carrierProductMap β)).comap (carrierProductMap α) = H := by
  rw [carrierTransport_quotient α β hβ]
  exact Subgroup.comap_map_eq_self (carrierProductMap_ker_le_of_axes α H haxis)

/-- The target projects onto each entire proper replacement group. -/
theorem carrierTransport_full (α : ∀ i, U i →* Q i) (β : ∀ i, P i →* Q i)
    (hα : ∀ i, Function.Surjective (α i)) (hβ : ∀ i, Function.Surjective (β i))
    (H : Subgroup (∀ i, U i)) (hH : CarrierProductFull H) :
    CarrierProductFull (carrierTransport α β H) := by
  intro i p
  obtain ⟨u,hu⟩ := hα i (β i p)
  obtain ⟨h,hh⟩ := hH i u
  choose d hd using fun j => hβ j (α j (h.1 j))
  let d' : ∀ j, P j := Function.update d i p
  refine ⟨⟨d',?_⟩,?_⟩
  · change carrierProductMap β d' ∈ H.map (carrierProductMap α)
    refine Subgroup.mem_map.mpr ⟨h.1,h.2,?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      simp only [carrierProductMap,MonoidHom.coe_mk,OneHom.coe_mk,d',Function.update_self]
      rw [hh,hu]
    · simpa [carrierProductMap,d',hj] using (hd j).symm
  · simp [d']

/-- Fixed decorated charts give an injection on actual source subgroups. -/
theorem carrierTransport_injective [Finite ι] [DecidableEq ι]
    (α : ∀ i, U i →* Q i) (β : ∀ i, P i →* Q i)
    (hβ : ∀ i, Function.Surjective (β i)) :
    Function.Injective (fun H : {H : Subgroup (∀ i, U i) //
      ∀ i, (α i).ker ≤ carrierAxis H i} => carrierTransport α β H.1) := by
  intro H K h
  change carrierTransport α β H.1 = carrierTransport α β K.1 at h
  apply Subtype.ext
  rw [← carrierTransport_reconstruct α β hβ H.1 H.2,
    ← carrierTransport_reconstruct α β hβ K.1 K.2,h]

section DisplayedCarriers

variable {κ : ι → Type*} {V : ∀ i, κ i → Type*} [∀ i j, Group (V i j)]
    (C : ∀ i, Subgroup (∀ j, V i j))

/-- Literal inclusion of each retained proper carrier into its displayed word. -/
def carrierReplacementEmbedding : (∀ i, C i) →* (∀ i j, V i j) where
  toFun p i j := (p i).1 j
  map_one' := rfl
  map_mul' _ _ := rfl

theorem carrierReplacementEmbedding_injective :
    Function.Injective (carrierReplacementEmbedding C) := by
  intro a b h
  funext i
  exact Subtype.ext (congrFun h i)

/-- Fullness is required on each displayed factor, not on each full block
product; the retained carrier within that product may be proper. -/
def CarrierDisplayedFull (H : Subgroup (∀ i j, V i j)) : Prop :=
  ∀ i j (v : V i j), ∃ h : H, h.1 i j = v

/-- The replacement as an actual subgroup in the original displayed ambient
word, retaining every internal carrier relation. -/
def carrierTransportInAmbient (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
    (H : Subgroup (∀ i, U i)) : Subgroup (∀ i j, V i j) :=
  (carrierTransport α β H).map (carrierReplacementEmbedding C)

theorem carrierTransportInAmbient_reconstruct [Finite ι] [DecidableEq ι]
    (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
    (hβ : ∀ i, Function.Surjective (β i)) (H : Subgroup (∀ i, U i))
    (haxis : ∀ i, (α i).ker ≤ carrierAxis H i) :
    (((carrierTransportInAmbient C α β H).comap (carrierReplacementEmbedding C)).map
      (carrierProductMap β)).comap (carrierProductMap α) = H := by
  unfold carrierTransportInAmbient
  rw [Subgroup.comap_map_eq_self_of_injective (carrierReplacementEmbedding_injective C)]
  exact carrierTransport_reconstruct α β hβ H haxis

theorem carrierTransportInAmbient_full
    (hC : ∀ i, CarrierProductFull (C i))
    (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
    (hα : ∀ i, Function.Surjective (α i)) (hβ : ∀ i, Function.Surjective (β i))
    (H : Subgroup (∀ i, U i)) (hH : CarrierProductFull H) :
    CarrierDisplayedFull (carrierTransportInAmbient C α β H) := by
  intro i j v
  obtain ⟨p,hp⟩ := hC i j v
  obtain ⟨h,hh⟩ := carrierTransport_full α β hα hβ H hH i p
  refine ⟨⟨carrierReplacementEmbedding C h.1,Subgroup.mem_map.mpr ⟨h.1,h.2,rfl⟩⟩,?_⟩
  change (h.1 i).1 j = v
  rw [hh]
  exact hp

/-- Original records retain the exact literal normal axes as decorations. -/
abbrev CarrierTransportSource [DecidableEq ι] (α : ∀ i, U i →* Q i) :=
  {H : Subgroup (∀ i, U i) // CarrierProductFull H ∧
    ∀ i, carrierAxis H i = (α i).ker}

/-- The target consists of actual full displayed-word subgroups. -/
abbrev CarrierTransportTarget := {H : Subgroup (∀ i j, V i j) // CarrierDisplayedFull H}

def carrierTransportRecords [DecidableEq ι]
    (hC : ∀ i, CarrierProductFull (C i))
    (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
    (hα : ∀ i, Function.Surjective (α i)) (hβ : ∀ i, Function.Surjective (β i)) :
    CarrierTransportSource α → CarrierTransportTarget (V := V) :=
  fun H => ⟨carrierTransportInAmbient C α β H.1,
    carrierTransportInAmbient_full C hC α β hα hβ H.1 H.2.1⟩

theorem carrierTransportRecords_injective [Finite ι] [DecidableEq ι]
    (hC : ∀ i, CarrierProductFull (C i))
    (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
    (hα : ∀ i, Function.Surjective (α i)) (hβ : ∀ i, Function.Surjective (β i)) :
    Function.Injective (carrierTransportRecords C hC α β hα hβ) := by
  intro H K h
  have hh : carrierTransportInAmbient C α β H.1 = carrierTransportInAmbient C α β K.1 :=
    congrArg (fun H : CarrierTransportTarget (V := V) => H.1) h
  apply Subtype.ext
  have hH : ∀ i, (α i).ker ≤ carrierAxis H.1 i := fun i => (H.2.2 i).ge
  have hK : ∀ i, (α i).ker ≤ carrierAxis K.1 i := fun i => (K.2.2 i).ge
  rw [← carrierTransportInAmbient_reconstruct C α β hβ H.1 hH,
    ← carrierTransportInAmbient_reconstruct C α β hβ K.1 hK,hh]

/-- For a fixed decorated profile the transport bounds the actual full
subgroup count, even with nonabelian proper subdirect carriers. -/
theorem carrierTransport_card_le [Finite ι] [DecidableEq ι] [∀ i, Finite (κ i)]
    [∀ i j, Finite (V i j)] (hC : ∀ i, CarrierProductFull (C i))
    (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
    (hα : ∀ i, Function.Surjective (α i)) (hβ : ∀ i, Function.Surjective (β i)) :
    Nat.card (CarrierTransportSource α) ≤ Nat.card (CarrierTransportTarget (V := V)) :=
  Nat.card_le_card_of_injective _ (carrierTransportRecords_injective C hC α β hα hβ)

/-- Every fixed original action/occurrence weight is retained literally.
No replacement normalizer weight is substituted during the comparison. -/
theorem carrierTransport_original_weight_le [Finite ι] [DecidableEq ι]
    [∀ i, Finite (κ i)] [∀ i j, Finite (V i j)]
    (hC : ∀ i, CarrierProductFull (C i))
    (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
    (hα : ∀ i, Function.Surjective (α i)) (hβ : ∀ i, Function.Surjective (β i))
    (w : ℝ) (hw : 0 ≤ w) :
    w * (Nat.card (CarrierTransportSource α) : ℝ) ≤
      w * (Nat.card (CarrierTransportTarget (V := V)) : ℝ) := by
  apply mul_le_mul_of_nonneg_left _ hw
  exact_mod_cast carrierTransport_card_le C hC α β hα hβ

end DisplayedCarriers

end SymmetricSubgroupAsymptotics
