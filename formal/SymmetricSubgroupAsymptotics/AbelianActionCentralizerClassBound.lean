import SymmetricSubgroupAsymptotics.AbelianActionClassBound
import SymmetricSubgroupAsymptotics.CentralizerClassBound

/-! The exact identity contribution in the complement centralizer sum
removes the additive translation cost in the fixed-space class bound.
Both capacities refer to the actual complement and translation group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AbelianActionCentralizerClassBound

theorem centralizer_card_le_of_injective {A G : Type*} [Group A] [Group G]
    [Finite A] [Finite G] (f : A →* G) (hf : Function.Injective f) (c : ℕ)
    (hc : ∀ g : G, g≠1 → Nat.card {h : G // Commute g h} ≤ c)
    (a : A) (ha : a≠1) : Nat.card {b : A // Commute a b} ≤ c := by
  have hfa : f a≠1 := by
    intro he
    exact ha (hf (he.trans (map_one f).symm))
  apply le_trans ?_ (hc (f a) hfa)
  apply Nat.card_le_card_of_injective
    (fun b : {b : A // Commute a b} =>
      (⟨f b.val,by
        have he := congrArg f b.property
        simpa only [map_mul] using he⟩ : {h : G // Commute (f a) h}))
  intro x y hxy
  exact Subtype.ext (hf (congrArg Subtype.val hxy))

theorem class_card_mul_le_of_injective {A G : Type*} [Group A] [Group G]
    [Finite A] [Finite G] (f : A →* G) (hf : Function.Injective f) (c : ℕ)
    (hc : ∀ g : G, g≠1 → Nat.card {h : G // Commute g h} ≤ c) :
    Nat.card A*Nat.card (ConjClasses A) ≤ Nat.card A+(Nat.card A-1)*c :=
  CentralizerClassBound.class_card_mul_le c
    (centralizer_card_le_of_injective f hf c hc)

theorem semidirect_class_card_le {N H : Type*} [CommGroup N] [Group H]
    [Finite N] [Finite H] (phi : H →* MulAut N) (d c : ℕ)
    (hfixed : ∀ h : H, h≠1 → Nat.card {n : N // phi h n=n} ≤ d)
    (hcent : ∀ h : H, h≠1 → Nat.card {k : H // Commute h k} ≤ c)
    (hcapacity : Nat.card N ≤ d*c) :
    Nat.card (ConjClasses (N ⋊[phi] H)) ≤ d*(c+1) := by
  have hc := CentralizerClassBound.class_card_mul_le c hcent
  have hs := AbelianActionClassBound.class_card_mul_complement_le phi d hfixed
  have hh : Nat.card H-1+1=Nat.card H := Nat.sub_add_cancel (Nat.card_pos (α := H))
  have he : d*c+d*Nat.card H+d*((Nat.card H-1)*c)=Nat.card H*(d*(c+1)) := by
    calc
      _ = d*Nat.card H+d*c*((Nat.card H-1)+1) := by ring
      _ = _ := by rw [hh]; ring
  have hbound : Nat.card H*Nat.card (ConjClasses (N ⋊[phi] H)) ≤
      Nat.card H*(d*(c+1)) := by
    calc
      _ ≤ Nat.card N+d*(Nat.card H*Nat.card (ConjClasses H)) := hs
      _ ≤ Nat.card N+d*(Nat.card H+(Nat.card H-1)*c) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left d hc) _
      _ = Nat.card N+d*Nat.card H+d*((Nat.card H-1)*c) := by ring
      _ ≤ d*c+d*Nat.card H+d*((Nat.card H-1)*c) :=
        Nat.add_le_add_right (Nat.add_le_add_right hcapacity _) _
      _ = _ := he
  exact Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α := H))

end SymmetricSubgroupAsymptotics.AbelianActionCentralizerClassBound
