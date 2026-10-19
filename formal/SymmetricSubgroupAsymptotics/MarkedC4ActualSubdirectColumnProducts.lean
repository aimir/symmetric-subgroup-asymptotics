import SymmetricSubgroupAsymptotics.MarkedC4ActualSubdirectFiltration
import SymmetricSubgroupAsymptotics.MarkedC4ActualLayerImageCard

/-! The TWO actual abelianization column products of a literal subdirect
source. Both use the SAME «prefix» chain, diagonal groups and lifted sets.
No independent maximal source types or character-extension assumption occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualSubdirectColumnProducts
open ActualSubdirectFiltration

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i)) (hsurj : ∀ i,Function.Surjective (coordinate F H i))

abbrev Abelian := Abelianization H

def generators (i : Fin t) : Finset H :=
  Classical.choose (exists_layer_generators F H hsurj i)

theorem generators_spec (i : Fin t) :
    (generators F H hsurj i).card≤normalGen (diagonal F H i) ∧
    (generators F H hsurj i : Set H) ⊆ «prefix» F H (i.val+1) ∧
    «prefix» F H (i.val+1)≤Subgroup.normalClosure (generators F H hsurj i : Set H) ⊔
      «prefix» F H i.val :=
  Classical.choose_spec (exists_layer_generators F H hsurj i)

def chain (m : ℕ) : Subgroup (Abelian F H) := («prefix» F H m).map Abelianization.of

def sets (m : ℕ) : Finset (Abelian F H) :=
  if hm : m<t then (generators F H hsurj ⟨m,hm⟩).image Abelianization.of else ∅

def layerOrder (m : ℕ) : ℕ :=
  if hm : m<t then Nat.card (diagonal F H ⟨m,hm⟩) else 1

theorem chain_zero : chain F H 0=⊥ := by
  unfold chain
  rw [prefix_zero,Subgroup.map_bot]

theorem chain_full : chain F H t=⊤ := by
  unfold chain
  rw [prefix_full]
  apply Subgroup.map_top_of_surjective
  intro a
  induction a using Quotient.inductionOn' with
  | h g => exact ⟨g,rfl⟩

theorem chain_mono (m : ℕ) : chain F H m≤chain F H (m+1) :=
  Subgroup.map_mono (prefix_mono F H m)

/-- The actual lifted normal generators map to ordinary closure generators
in the SAME abelianized «prefix» layer. -/
theorem chain_step (m : ℕ) (hm : m<t) :
    chain F H (m+1)≤Subgroup.closure (sets F H hsurj m : Set (Abelian F H)) ⊔ chain F H m := by
  let i : Fin t := ⟨m,hm⟩
  have hstep := (generators_spec F H hsurj i).2.2
  have hmap := Subgroup.map_mono (f := (Abelianization.of : H →* Abelian F H)) hstep
  rw [Subgroup.map_sup] at hmap
  have hc : (Subgroup.normalClosure (generators F H hsurj i : Set H)).map Abelianization.of ≤
      Subgroup.closure ((generators F H hsurj i).image Abelianization.of : Set (Abelian F H)) := by
    apply (Subgroup.map_normalClosure_le _ _).trans
    apply Subgroup.normalClosure_le_normal
    intro x hx
    apply Subgroup.subset_closure
    simpa only [Finset.coe_image] using hx
  have hh := hmap.trans (sup_le_sup hc le_rfl)
  simpa only [chain,sets,dif_pos hm] using hh

/-- The cardinal factor is the SAME actual diagonal, proved through the
actual coordinate factorization rather than a separate worst-case rank. -/
theorem chain_card_step (m : ℕ) (hm : m<t) :
    Nat.card (chain F H (m+1))≤layerOrder F H m*Nat.card (chain F H m) := by
  have hh := ActualLayerImageCard.image_layer_card_le
    (Abelianization.of : H →* Abelian F H) (coordinate F H ⟨m,hm⟩)
    («prefix» F H m) («prefix» F H (m+1)) (prefix_mono F H m)
    (prefix_kernel F H ⟨m,hm⟩)
  simpa only [chain,layerOrder,dif_pos hm,diagonal] using hh

/-- BOTH binary column capacities are instances of one concrete cardinal
filtration, with identical physical groups and identical generator sets. -/
theorem quotient_power_product (k : ℕ) (hk : 0<k) :
    Nat.card (Abelian F H ⧸ powSub (Abelian F H) k) ≤
      ∏ m ∈ Finset.range t,min (k^(sets F H hsurj m).card) (layerOrder F H m) :=
  card_quotient_pow_le_of_chain k hk t (chain F H) (chain_zero F H) (chain_full F H)
    (chain_mono F H) (sets F H hsurj) (layerOrder F H)
    (chain_step F H hsurj) (chain_card_step F H)

theorem first_column_product :
    2^col (Abelian F H) 0 ≤
      ∏ m ∈ Finset.range t,min (2^(sets F H hsurj m).card) (layerOrder F H m) := by
  have h := quotient_power_product F H hsurj 2 (by omega)
  rw [card_quotient_powSub_two] at h
  exact h

theorem two_columns_product :
    2^(col (Abelian F H) 0+col (Abelian F H) 1) ≤
      ∏ m ∈ Finset.range t,min (4^(sets F H hsurj m).card) (layerOrder F H m) := by
  have h := quotient_power_product F H hsurj 4 (by omega)
  rw [card_quotient_powSub_four] at h
  exact h

end SymmetricSubgroupAsymptotics.MarkedC4.ActualSubdirectColumnProducts
