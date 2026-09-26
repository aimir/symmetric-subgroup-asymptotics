import SymmetricSubgroupAsymptotics.BinaryMixtureCentralComparison
import SymmetricSubgroupAsymptotics.BinaryTargetOrderEnvelope
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! Replacing a finite binary group by the elementary abelian group of the
same order can only increase subgroup counts, even with an arbitrary finite
exterior group and an arbitrary predicate on its exact subgroup image.
Each induction step uses an actual central subgroup of order two. There is
no group embedding from the original binary group into the comparison group.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPGroupExteriorComparison

abbrev Binary (n : ℕ) := Multiplicative (Fin n → ZMod 2)
abbrev Bit := Multiplicative (ZMod 2)

private def imageFilteredEquiv {G H E : Type*} [Group G] [Group H] [Group E]
    (e : G ≃* H) (f : G →* E) (g : H →* E)
    (he : g.comp e.toMonoidHom = f) (P : Subgroup E → Prop) :
    {K : Subgroup G // P (K.map f)} ≃ {K : Subgroup H // P (K.map g)} :=
  e.mapSubgroup.toEquiv.subtypeEquiv (fun K => by
    change P (K.map f) ↔ P ((K.map e.toMonoidHom).map g)
    rw [Subgroup.map_map, he])

section CentralStep

variable (E B : Type*) [Group E] [Group B] (C : Subgroup B) [C.Normal]

/-- Quotient only the binary factor; the complete exterior is unchanged. -/
def projection : (E × B) →* (E × (B ⧸ C)) :=
  (MonoidHom.id E).prodMap (QuotientGroup.mk' C)

theorem projection_surjective : Function.Surjective (projection E B C) := by
  rintro ⟨e, q⟩
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective C q
  exact ⟨(e, b), Prod.ext rfl hb⟩

/-- The kernel is exactly the original C, in the original binary factor. -/
def projectionKernel : C ≃* (projection E B C).ker where
  toFun c := ⟨(1, c.1), by
    apply Prod.ext
    · rfl
    · exact (QuotientGroup.eq_one_iff c.1).mpr c.2⟩
  invFun k := ⟨k.1.2, (QuotientGroup.eq_one_iff k.1.2).mp (congrArg Prod.snd k.2)⟩
  left_inv _ := rfl
  right_inv k := by
    apply Subtype.ext
    exact Prod.ext (congrArg Prod.fst k.2).symm rfl
  map_mul' _ _ := by
    apply Subtype.ext
    exact Prod.ext (one_mul 1).symm rfl

theorem projectionKernel_central (hC : C ≤ Subgroup.center B) :
    (projection E B C).ker ≤ Subgroup.center (E × B) := by
  intro k hk
  have he : k.1 = 1 := congrArg Prod.fst hk
  have hb : k.2 ∈ C := (QuotientGroup.eq_one_iff k.2).mp (congrArg Prod.snd hk)
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Prod.ext
  · simp only [Prod.fst_mul, he, mul_one, one_mul]
  · exact Subgroup.mem_center_iff.mp (hC hb) x.2

end CentralStep

private def binaryStepChart (n : ℕ) :
    (ZMod 2 × (Fin n → ZMod 2)) ≃ₗ[ZMod 2] (Fin (n+1) → ZMod 2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
      Fintype.card_fin]
    omega)

private def binaryStepEquiv (n : ℕ) : (Bit × Binary n) ≃* Binary (n+1) :=
  let e : (Bit × Binary n) ≃* Multiplicative (ZMod 2 × (Fin n → ZMod 2)) :=
    (MulEquiv.prodMultiplicative (G := ZMod 2) (H := Fin n → ZMod 2)).symm
  e.trans (binaryStepChart n).toAddEquiv.toMultiplicative

/-- Move the newly split bit beside the previously split binary block,
retaining the exterior coordinate literally. -/
private def regroup (E : Type*) [Group E] (n : ℕ) :
    ((Bit × E) × Binary n) ≃* (E × Binary (n+1)) where
  toFun x := (x.1.2, binaryStepEquiv n (x.1.1, x.2))
  invFun y := ((((binaryStepEquiv n).symm y.2).1, y.1),
    ((binaryStepEquiv n).symm y.2).2)
  left_inv x := by
    have h := (binaryStepEquiv n).symm_apply_apply (x.1.1, x.2)
    apply Prod.ext
    · apply Prod.ext
      · change ((binaryStepEquiv n).symm (binaryStepEquiv n (x.1.1, x.2))).1 = x.1.1
        exact congrArg (fun z : Bit × Binary n => z.1) h
      · rfl
    · change ((binaryStepEquiv n).symm (binaryStepEquiv n (x.1.1, x.2))).2 = x.2
      exact congrArg (fun z : Bit × Binary n => z.2) h
  right_inv y := Prod.ext rfl ((binaryStepEquiv n).apply_symm_apply y.2)
  map_mul' x y := by
    apply Prod.ext
    · rfl
    · change binaryStepEquiv n (x.1.1 * y.1.1, x.2 * y.2) =
        binaryStepEquiv n (x.1.1, x.2) * binaryStepEquiv n (y.1.1, y.2)
      exact (binaryStepEquiv n).map_mul (x.1.1, x.2) (y.1.1, y.2)

local instance subgroupFinite {G : Type*} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- The comparison retains every condition on the literal exterior image.
The original binary factor is specified by its actual cardinality; this
already implies that it is a finite 2-group. -/
theorem filtered_subgroup_card_le (E B : Type*) [Group E] [Finite E]
    [Group B] [Finite B] (n : ℕ) (hB : Nat.card B = 2^n)
    (P : Subgroup E → Prop) :
    Nat.card {H : Subgroup (E × B) // P (H.map (MonoidHom.fst E B))} ≤
      Nat.card {H : Subgroup (E × Binary n) //
        P (H.map (MonoidHom.fst E (Binary n)))} := by
  classical
  induction n generalizing E B with
  | zero =>
    letI : Subsingleton B := (Nat.card_eq_one_iff_unique.mp (by simpa using hB)).1
    let eB : B ≃* Binary 0 :=
      { toFun := fun _ => 1
        invFun := fun _ => 1
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        map_mul' := fun _ _ => (one_mul 1).symm }
    exact (Nat.card_congr (imageFilteredEquiv
      ((MulEquiv.refl E).prodCongr eB)
      (MonoidHom.fst E B) (MonoidHom.fst E (Binary 0)) rfl P)).le
  | succ n ih =>
    have hp : 0 < 2^n := pow_pos (by decide) n
    letI : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hB, pow_succ]
      omega)
    obtain ⟨C, hC, hc⟩ := binaryTargetOrder_exists_central_two (IsPGroup.of_card hB)
    letI : C.Normal := ⟨by
      intro c hc' b
      have hcomm : Commute b c := Subgroup.mem_center_iff.mp (hC hc') b
      rw [hcomm.mul_inv_cancel]
      exact hc'⟩
    have hquot : Nat.card (B ⧸ C) = 2^n := by
      have hm := Subgroup.card_eq_card_quotient_mul_card_subgroup C
      rw [hB, hc, pow_succ] at hm
      omega
    let eC : Bit ≃* C := mulEquivOfPrimeCardEq (by simp) hc
    have hstep :
        Nat.card {H : Subgroup (E × B) // P (H.map (MonoidHom.fst E B))} ≤
          Nat.card {H : Subgroup (Bit × (E × (B ⧸ C))) //
            P (H.map ((MonoidHom.fst E (B ⧸ C)).comp
              (MonoidHom.snd Bit (E × (B ⧸ C)))))} := by
      have h := binaryCentral_filtered_card_le_split (projection E B C)
        (eC.trans (projectionKernel E B C)) (projection_surjective E B C)
        (projectionKernel_central E B C hC)
        (fun L => P (L.map (MonoidHom.fst E (B ⧸ C))))
      simpa only [Subgroup.map_map] using h
    have hassoc :
        Nat.card {H : Subgroup (Bit × (E × (B ⧸ C))) //
          P (H.map ((MonoidHom.fst E (B ⧸ C)).comp
            (MonoidHom.snd Bit (E × (B ⧸ C)))))} =
        Nat.card {H : Subgroup ((Bit × E) × (B ⧸ C)) //
          P ((H.map (MonoidHom.fst (Bit × E) (B ⧸ C))).map
            (MonoidHom.snd Bit E))} := by
      simpa only [Subgroup.map_map] using Nat.card_congr
        (imageFilteredEquiv (MulEquiv.prodAssoc :
            ((Bit × E) × (B ⧸ C)) ≃* (Bit × (E × (B ⧸ C)))).symm
          ((MonoidHom.fst E (B ⧸ C)).comp (MonoidHom.snd Bit (E × (B ⧸ C))))
          ((MonoidHom.snd Bit E).comp (MonoidHom.fst (Bit × E) (B ⧸ C)))
          (by apply MonoidHom.ext; intro x; rfl) P)
    have hfinal :
        Nat.card {H : Subgroup ((Bit × E) × Binary n) //
          P ((H.map (MonoidHom.fst (Bit × E) (Binary n))).map
            (MonoidHom.snd Bit E))} =
        Nat.card {H : Subgroup (E × Binary (n+1)) //
          P (H.map (MonoidHom.fst E (Binary (n+1))))} := by
      simpa only [Subgroup.map_map] using Nat.card_congr
        (imageFilteredEquiv (regroup E n)
          ((MonoidHom.snd Bit E).comp (MonoidHom.fst (Bit × E) (Binary n)))
          (MonoidHom.fst E (Binary (n+1)))
          (by apply MonoidHom.ext; intro x; rfl) P)
    exact hstep.trans (hassoc.le.trans
      ((ih (Bit × E) (B ⧸ C) hquot (fun L => P (L.map (MonoidHom.snd Bit E)))).trans
        hfinal.le))

/-- In particular the complete original product has no more subgroups
than the product with an elementary abelian factor of the same order. -/
theorem subgroup_card_le (E B : Type*) [Group E] [Finite E]
    [Group B] [Finite B] (n : ℕ) (hB : Nat.card B = 2^n) :
    Nat.card (Subgroup (E × B)) ≤ Nat.card (Subgroup (E × Binary n)) := by
  simpa using filtered_subgroup_card_le E B n hB (fun _ => True)

end SymmetricSubgroupAsymptotics.BinaryPGroupExteriorComparison
