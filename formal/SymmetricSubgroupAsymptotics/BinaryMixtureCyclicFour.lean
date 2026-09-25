import SymmetricSubgroupAsymptotics.BinaryMixtureCentralComparison

/-!
# The actual cyclic-four to binary comparison

The quotient is reduction modulo two in each original C4 coordinate and the
identity on the entire exterior. Its central kernel is charted explicitly.
The comparison preserves every condition on the exact exterior image.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

def cyclicFourReduction : ZMod 4 →+ ZMod 2 :=
  (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)).toAddMonoidHom

def cyclicFourDouble : ZMod 2 →+ ZMod 4 where
  toFun z := 2*(z.val : ZMod 4)
  map_zero' := by decide
  map_add' := by decide

def cyclicFourHalf (z : ZMod 4) : ZMod 2 := if z = 0 then 0 else 1

theorem cyclicFourReduction_double (z : ZMod 2) :
    cyclicFourReduction (cyclicFourDouble z) = 0 := by
  revert z
  decide

theorem cyclicFourHalf_double (z : ZMod 2) :
    cyclicFourHalf (cyclicFourDouble z) = z := by
  revert z
  decide

theorem cyclicFourDouble_half (z : ZMod 4) (hz : cyclicFourReduction z = 0) :
    cyclicFourDouble (cyclicFourHalf z) = z := by
  revert z
  decide

variable (G : Type*) [Group G]

/-- Reduction on all original cyclic-four factors, identity on the complete
possibly nonabelian exterior. -/
def cyclicFourProductProjection (a : ℕ) :
    (Multiplicative (Fin a → ZMod 4) × G) →*
      (Multiplicative (Fin a → ZMod 2) × G) where
  toFun x := (Multiplicative.ofAdd (fun i => cyclicFourReduction (x.1.toAdd i)),x.2)
  map_one' := by
    apply Prod.ext
    · exact congrArg Multiplicative.ofAdd (funext fun _ => map_zero cyclicFourReduction)
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext i
      exact map_add cyclicFourReduction _ _
    · rfl

theorem cyclicFourProductProjection_surjective (a : ℕ) :
    Function.Surjective (cyclicFourProductProjection G a) := by
  rintro ⟨v,g⟩
  have hs : Function.Surjective cyclicFourReduction :=
    ZMod.castHom_surjective (show 2 ∣ 4 by decide)
  choose z hz using fun i => hs (v.toAdd i)
  refine ⟨(Multiplicative.ofAdd z,g),Prod.ext ?_ rfl⟩
  exact congrArg Multiplicative.ofAdd (funext hz)

/-- The complete original central kernel, with each involution retained. -/
def cyclicFourProductKernel (a : ℕ) :
    Multiplicative (Fin a → ZMod 2) ≃* (cyclicFourProductProjection G a).ker where
  toFun v := ⟨(Multiplicative.ofAdd (fun i => cyclicFourDouble (v.toAdd i)),1),by
    apply Prod.ext
    · exact congrArg Multiplicative.ofAdd (funext fun i => cyclicFourReduction_double (v.toAdd i))
    · rfl⟩
  invFun x := Multiplicative.ofAdd (fun i => cyclicFourHalf (x.1.1.toAdd i))
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    exact cyclicFourHalf_double _
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext i
      apply cyclicFourDouble_half
      exact congrArg (fun y : Multiplicative (Fin a → ZMod 2) × G => y.1.toAdd i) x.2
    · exact (congrArg Prod.snd x.2).symm
  map_mul' v w := by
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext i
      exact map_add cyclicFourDouble _ _
    · simp

theorem cyclicFourProductKernel_central (a : ℕ) :
    (cyclicFourProductProjection G a).ker ≤
      Subgroup.center (Multiplicative (Fin a → ZMod 4) × G) := by
  intro k hk
  have hg : k.2 = 1 := congrArg Prod.snd hk
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Prod.ext
  · exact mul_comm _ _
  · simp only [Prod.snd_mul,hg,mul_one,one_mul]

/-- Projection from the two binary blocks to the same complete exterior. -/
def cyclicFourSplitExterior (a : ℕ) :
    (Multiplicative (Fin a → ZMod 2) × (Multiplicative (Fin a → ZMod 2) × G)) →* G :=
  (MonoidHom.snd (Multiplicative (Fin a → ZMod 2)) G).comp
    (MonoidHom.snd (Multiplicative (Fin a → ZMod 2)) _)

/-- All C4 coordinates may be replaced simultaneously by two equally sized
binary blocks, preserving every actual exterior-image predicate. -/
theorem cyclicFour_filtered_card_le_two_binary [Finite G] (a : ℕ)
    (P : Subgroup G → Prop) :
    Nat.card {H : Subgroup (Multiplicative (Fin a → ZMod 4) × G) //
      P (H.map (MonoidHom.snd _ G))} ≤
    Nat.card {H : Subgroup (Multiplicative (Fin a → ZMod 2) ×
        (Multiplicative (Fin a → ZMod 2) × G)) //
      P (H.map (cyclicFourSplitExterior G a))} := by
  have h := binaryCentral_filtered_card_le_split (cyclicFourProductProjection G a)
    (cyclicFourProductKernel G a) (cyclicFourProductProjection_surjective G a)
    (cyclicFourProductKernel_central G a)
    (fun L => P (L.map (MonoidHom.snd (Multiplicative (Fin a → ZMod 2)) G)))
  simpa only [Subgroup.map_map] using h

/-- Fullness on the original C4 coordinates is dropped only after the
complete exterior image has been retained by the generic comparison. -/
theorem cyclicFour_full_filtered_card_le_two_binary [Finite G] (a : ℕ)
    (P : Subgroup G → Prop) :
    Nat.card {H : Subgroup (Multiplicative (Fin a → ZMod 4) × G) //
      (∀ i (z : ZMod 4), ∃ h : H, h.1.1.toAdd i = z) ∧
      P (H.map (MonoidHom.snd _ G))} ≤
    Nat.card {H : Subgroup (Multiplicative (Fin a → ZMod 2) ×
        (Multiplicative (Fin a → ZMod 2) × G)) //
      P (H.map (cyclicFourSplitExterior G a))} := by
  apply le_trans _ (cyclicFour_filtered_card_le_two_binary G a P)
  apply Nat.card_le_card_of_injective
    (fun H => (⟨H.1,H.2.2⟩ : {H : Subgroup (Multiplicative (Fin a → ZMod 4) × G) //
      P (H.map (MonoidHom.snd _ G))}))
  intro H K h
  exact Subtype.ext (congrArg (fun H : {H : Subgroup (Multiplicative (Fin a → ZMod 4) × G) //
    P (H.map (MonoidHom.snd _ G))} => H.1) h)

end SymmetricSubgroupAsymptotics
