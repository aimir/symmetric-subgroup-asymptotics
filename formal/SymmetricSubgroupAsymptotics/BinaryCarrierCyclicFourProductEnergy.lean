import SymmetricSubgroupAsymptotics.BinaryMixtureCyclicFour
import SymmetricSubgroupAsymptotics.BinaryCarrierWordProductEnergy
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! A cyclic-four product is bounded by the binary terminal reserve at
abelian rank a+2c. The central-comparison inequality retains the exact
exterior image; only its subsequent binary product is regrouped by an
equivalence. Arbitrary original survival is dropped by literal inclusion.
This upper bound alone gives no cyclic-four-only deficit when T=0; the
separate Hall comparison remains a distinct input for that regime.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCyclicFourProductEnergy

open BinaryCarrierWord

abbrev BinaryBlock (a : ℕ) := Multiplicative (Fin a → ZMod 2)

def binaryBlocksChart (a c : ℕ) :
    ((Fin c → ZMod 2) × ((Fin c → ZMod 2) × (Fin a → ZMod 2))) ≃ₗ[ZMod 2]
      (Fin (a+2*c) → ZMod 2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
    omega)

def binaryBlocksEquiv (a c : ℕ) :
    (BinaryBlock c × (BinaryBlock c × BinaryBlock a)) ≃* BinaryBlock (a+2*c) :=
  let e₁ : (BinaryBlock c × (BinaryBlock c × BinaryBlock a)) ≃*
      (BinaryBlock c × Multiplicative ((Fin c → ZMod 2) × (Fin a → ZMod 2))) :=
    (MulEquiv.refl (BinaryBlock c)).prodCongr
      (MulEquiv.prodMultiplicative (G := Fin c → ZMod 2)
        (H := Fin a → ZMod 2)).symm
  let e₂ : (BinaryBlock c × Multiplicative ((Fin c → ZMod 2) × (Fin a → ZMod 2))) ≃*
      Multiplicative ((Fin c → ZMod 2) × ((Fin c → ZMod 2) × (Fin a → ZMod 2))) :=
    (MulEquiv.prodMultiplicative (G := Fin c → ZMod 2)
      (H := (Fin c → ZMod 2) × (Fin a → ZMod 2))).symm
  (e₁.trans e₂).trans (binaryBlocksChart a c).toAddEquiv.toMultiplicative

private def gatherThreeBlocks {A B C H T : Type*}
    [Group A] [Group B] [Group C] [Group H] [Group T] :
    (A × (B × ((C × H) × T))) ≃* (((A × (B × C)) × H) × T) where
  toFun x := (((x.1,(x.2.1,x.2.2.1.1)),x.2.2.1.2),x.2.2.2)
  invFun y := (y.1.1.1,(y.1.1.2.1,((y.1.1.2.2,y.1.2),y.2)))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem card_subtype_conjunction_le {α : Type*} [Finite α]
    (Q P : α → Prop) :
    Nat.card {x : α // Q x ∧ P x} ≤ Nat.card {x : α // Q x} := by
  apply Nat.card_le_card_of_injective
    (fun x : {x : α // Q x ∧ P x} => (⟨x.1,x.2.1⟩ : {x : α // Q x}))
  intro x y h
  exact Subtype.ext (congrArg (fun z : {x : α // Q x} => z.1) h)

variable {ι : Type} [Fintype ι] (a c : ℕ) (s : ι → Bool) (w : List Factor)

abbrev Exterior := CriticalProductGroup a s × Product w

abbrev Comparison := BinaryBlock c × (BinaryBlock c × Exterior a s w)

/-- Only the three binary abelian blocks are regrouped. Every original
nonabelian critical coordinate and the entire carrier tuple are unchanged. -/
def regroup : Comparison a c s w ≃* (CriticalProductGroup (a+2*c) s × Product w) :=
  (gatherThreeBlocks (A := BinaryBlock c) (B := BinaryBlock c)
    (C := BinaryBlock a)
    (H := ∀ i, BinaryHeisenberg (criticalFactorHalfRank (s i)))
    (T := Product w)).trans
      (((binaryBlocksEquiv a c).prodCongr
        (MulEquiv.refl (∀ i, BinaryHeisenberg (criticalFactorHalfRank (s i))))).prodCongr
          (MulEquiv.refl (Product w)))

theorem regroup_tail_projection :
    (MonoidHom.snd _ (Product w)).comp (regroup a c s w).toMonoidHom =
      (MonoidHom.snd _ (Product w)).comp (cyclicFourSplitExterior (Exterior a s w) c) := by
  apply MonoidHom.ext
  intro x
  rfl

theorem regroup_factor_projection (i : ι) :
    ((criticalProductFactorProjection (a+2*c) s i).comp (MonoidHom.fst _ _)).comp
        (regroup a c s w).toMonoidHom =
      ((criticalProductFactorProjection a s i).comp (MonoidHom.fst _ _)).comp
        (cyclicFourSplitExterior (Exterior a s w) c) := by
  apply MonoidHom.ext
  intro x
  rfl

/-- No fullness is imposed on the whole critical-product projection or
on its binary abelian coordinates. -/
def ExteriorFull (H : Subgroup (Exterior a s w)) : Prop :=
  Full w (SubdirectTailImage.tail H) ∧ terminalCoordinatesFull a s H

theorem exteriorFull_regroup_iff (H : Subgroup (Comparison a c s w)) :
    ExteriorFull (a+2*c) s w (H.map (regroup a c s w).toMonoidHom) ↔
      ExteriorFull a s w (H.map (cyclicFourSplitExterior (Exterior a s w) c)) := by
  have ht : SubdirectTailImage.tail (H.map (regroup a c s w).toMonoidHom) =
      SubdirectTailImage.tail (H.map (cyclicFourSplitExterior (Exterior a s w) c)) := by
    change (H.map (regroup a c s w).toMonoidHom).map (MonoidHom.snd _ _) =
      (H.map (cyclicFourSplitExterior (Exterior a s w) c)).map (MonoidHom.snd _ _)
    rw [Subgroup.map_map,Subgroup.map_map]
    rw [regroup_tail_projection]
  have hc (i : ι) :
      (H.map (regroup a c s w).toMonoidHom).map
          ((criticalProductFactorProjection (a+2*c) s i).comp (MonoidHom.fst _ _)) =
        (H.map (cyclicFourSplitExterior (Exterior a s w) c)).map
          ((criticalProductFactorProjection a s i).comp (MonoidHom.fst _ _)) := by
    rw [Subgroup.map_map,Subgroup.map_map]
    rw [regroup_factor_projection]
  unfold ExteriorFull terminalCoordinatesFull
  simp only [ht,hc]

/-- The entire comparison family, including all binary-coordinate images,
is an exact terminal family after regrouping. -/
def comparisonEquivTerminal :
    {H : Subgroup (Comparison a c s w) //
      ExteriorFull a s w (H.map (cyclicFourSplitExterior (Exterior a s w) c))} ≃
      TerminalProductFamily (a+2*c) s w (fun _ => True) where
  toFun H :=
    ⟨H.1.map (regroup a c s w).toMonoidHom,
      ((exteriorFull_regroup_iff a c s w H.1).mpr H.2).1,
      ((exteriorFull_regroup_iff a c s w H.1).mpr H.2).2,True.intro⟩
  invFun K := ⟨K.1.comap (regroup a c s w).toMonoidHom,by
    apply (exteriorFull_regroup_iff a c s w _).mp
    rw [Subgroup.map_comap_eq_self_of_surjective
      (f := (regroup a c s w).toMonoidHom) (regroup a c s w).surjective]
    exact ⟨K.2.1,K.2.2.1⟩⟩
  left_inv H := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective (regroup a c s w).injective H.1
  right_inv K := by
    apply Subtype.ext
    exact Subgroup.map_comap_eq_self_of_surjective (regroup a c s w).surjective K.1

/-- P is a predicate on the original cyclic-four product subgroup. It can
include all original C4 fullness and arbitrary earlier survival conditions. -/
abbrev OriginalFamily
    (P : Subgroup (Multiplicative (Fin c → ZMod 4) × Exterior a s w) → Prop) :=
  {H : Subgroup (Multiplicative (Fin c → ZMod 4) × Exterior a s w) //
    ExteriorFull a s w (H.map (MonoidHom.snd _ _)) ∧ P H}

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- The sole loss of arbitrary original survival occurs by this literal
inclusion before applying the central-extension counting comparison. -/
theorem originalFamily_card_le_terminal
    (P : Subgroup (Multiplicative (Fin c → ZMod 4) × Exterior a s w) → Prop) :
    Nat.card (OriginalFamily a c s w P) ≤
      Nat.card (TerminalProductFamily (a+2*c) s w (fun _ => True)) := by
  letI : Finite (Subgroup (Multiplicative (Fin c → ZMod 4) × Exterior a s w)) :=
    subgroupFinite
  have hforget : Nat.card (OriginalFamily a c s w P) ≤
      Nat.card {H : Subgroup (Multiplicative (Fin c → ZMod 4) × Exterior a s w) //
        ExteriorFull a s w (H.map (MonoidHom.snd _ _))} :=
    card_subtype_conjunction_le
      (α := Subgroup (Multiplicative (Fin c → ZMod 4) × Exterior a s w))
      (fun H : Subgroup (Multiplicative (Fin c → ZMod 4) × Exterior a s w) =>
        ExteriorFull a s w
          (H.map (MonoidHom.snd (Multiplicative (Fin c → ZMod 4)) (Exterior a s w)))) P
  calc
    _ ≤ _ := hforget
    _ ≤ Nat.card {H : Subgroup (Comparison a c s w) //
        ExteriorFull a s w (H.map (cyclicFourSplitExterior (Exterior a s w) c))} :=
      cyclicFour_filtered_card_le_two_binary (Exterior a s w) c (ExteriorFull a s w)
    _ = _ := Nat.card_congr (comparisonEquivTerminal a c s w)

/-- A support split or a binomial sum is unnecessary for this upper bound,
because the terminal family already allows every binary abelian image. -/
theorem originalFamily_card_le_reserve (b : ℕ) (hb : OrderBound w b)
    (T : ℝ) (cert : CertifiedHistoryRows w T)
    (P : Subgroup (Multiplicative (Fin c → ZMod 4) × Exterior a s w) → Prop) :
    (Nat.card (OriginalFamily a c s w P) : ℝ) ≤
      terminalProductReserve (a+2*c) s b w.length T := by
  have h : (Nat.card (OriginalFamily a c s w P) : ℝ) ≤
      (Nat.card (TerminalProductFamily (a+2*c) s w (fun _ => True)) : ℝ) := by
    exact_mod_cast originalFamily_card_le_terminal a c s w P
  exact h.trans (terminal_product_subgroups_le_reserve_of_orderBound
    (a+2*c) s w b hb T cert (fun _ => True))

theorem regroup_rank : criticalProductRank (a+2*c) s = criticalProductRank a s + 2*c := by
  unfold criticalProductRank
  omega

end SymmetricSubgroupAsymptotics.BinaryCarrierCyclicFourProductEnergy
