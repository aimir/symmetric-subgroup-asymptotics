import SymmetricSubgroupAsymptotics.SimpleCoordinateSupportCover
import SymmetricSubgroupAsymptotics.SimplePowerFullSubdirectCount

/-! Count every literal zero/full coordinate support and every complete
subdirect on it. The support is recovered before counting, and all
proper diagonals and automorphism twists remain in the subdirect code.
No transitivity or one-minimal-normal-orbit hypothesis is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SimpleCoordinateSupportCount

variable (T : Type) [Group T] [Finite T] [IsSimpleGroup T]

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

abbrev Full (I : Type) :=
  {H : Subgroup (I → T) // ∀ i : I,Function.Surjective (fun h : H => h.val i)}

def powerReindex (I : Type) [Finite I] : (I → T) ≃* (Fin (Nat.card I) → T) where
  toFun f i := f ((Finite.equivFin I).symm i)
  invFun f i := f (Finite.equivFin I i)
  left_inv f := by funext i; exact congrArg f ((Finite.equivFin I).symm_apply_apply i)
  right_inv f := by funext i; exact congrArg f ((Finite.equivFin I).apply_symm_apply i)
  map_mul' _ _ := rfl

def fullReindex (I : Type) [Finite I] (H : Full T I) :
    SimplePowerFullSubdirectCount.Family T (Nat.card I) := by
  let e := powerReindex T I
  refine ⟨H.val.map e.toMonoidHom,?_⟩
  intro i t
  obtain ⟨h,hh⟩ := H.property ((Finite.equivFin I).symm i) t
  exact ⟨⟨e h.val,⟨h.val,h.property,rfl⟩⟩,hh⟩

omit [Finite T] [IsSimpleGroup T] in
theorem fullReindex_injective (I : Type) [Finite I] :
    Function.Injective (fullReindex T I) := by
  intro H K h
  apply Subtype.ext
  exact Subgroup.map_injective (powerReindex T I).injective
    (congrArg (fun z : SimplePowerFullSubdirectCount.Family T (Nat.card I) => z.val) h)

theorem card_full_le (hZ : IsCenterless T) (I : Type) [Finite I] :
    Nat.card (Full T I) ≤
      (2*(1+Nat.card I*Nat.card (T ≃* T)))^(Nat.card I) :=
  (Nat.card_le_card_of_injective (fullReindex T I) (fullReindex_injective T I)).trans
    (SimplePowerFullSubdirectCount.card_family_le T hZ (Nat.card I))

/-- Whole normal-coordinate family, summed over ALL literal supports. -/
theorem card_family_le (hZ : IsCenterless T) (I : Type) [Finite I] :
    Nat.card (SimpleCoordinateSupportCover.Family (fun _ : I => T)) ≤
      2^(Nat.card I)*(2*(1+Nat.card I*Nat.card (T ≃* T)))^(Nat.card I) := by
  letI : Fintype I := Fintype.ofFinite _
  let B := 2*(1+Nat.card I*Nat.card (T ≃* T))
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hs (s : Set I) :
      Nat.card (SimpleCoordinateSupportCover.FullOn (fun _ : I => T) s) ≤ B^(Nat.card I) := by
    have hm : Nat.card s ≤ Nat.card I := Finite.card_subtype_le _
    have hb : 2*(1+Nat.card s*Nat.card (T ≃* T)) ≤ B :=
      Nat.mul_le_mul_left 2 (Nat.add_le_add_left
        (Nat.mul_le_mul_right (Nat.card (T ≃* T)) hm) 1)
    exact (card_full_le T hZ s).trans
      ((Nat.pow_le_pow_left hb (Nat.card s)).trans (Nat.pow_le_pow_right hB hm))
  have hsets : Nat.card (Set I)=2^Nat.card I := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_set]
  calc
    Nat.card (SimpleCoordinateSupportCover.Family (fun _ : I => T)) ≤
        Nat.card (Σ s : Set I,SimpleCoordinateSupportCover.FullOn (fun _ : I => T) s) :=
      Nat.card_le_card_of_injective (SimpleCoordinateSupportCover.code (fun _ : I => T))
        (SimpleCoordinateSupportCover.code_injective (fun _ : I => T))
    _ = ∑ s : Set I,Nat.card
        (SimpleCoordinateSupportCover.FullOn (fun _ : I => T) s) := Nat.card_sigma
    _ ≤ ∑ _s : Set I,B^(Nat.card I) := Finset.sum_le_sum (fun s _ => hs s)
    _ = Nat.card (Set I)*B^(Nat.card I) := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
    _ = 2^(Nat.card I)*(2*(1+Nat.card I*Nat.card (T ≃* T)))^(Nat.card I) := by
      rw [hsets]

end SymmetricSubgroupAsymptotics.SimpleCoordinateSupportCount
