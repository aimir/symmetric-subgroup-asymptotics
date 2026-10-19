import SymmetricSubgroupAsymptotics.MarkedC4ActualPhysicalPeelPackets

/-! The actual enlarged word family is closed under a physical peel.
Only one mark group M remains, including arbitrary vertical mark subgroups.
The packet retains an actual source in the SAME smaller physical family. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualFullPhysicalWordPeel

abbrev Family {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)]
    (M : Type) [Group M] := {J : Subgroup ((∀ i,F i) × M) //
      ∀ i,Function.Surjective (fun h : J => h.val.1 i)}

variable {t : ℕ} (F : Fin (t+1) → Type) [∀ i,Group (F i)] (M : Type) [Group M]
abbrev TailFactors := fun j : Fin t => F j.succ
abbrev TailAmbient := (∀ j,TailFactors F j) × M

def split : ((∀ i,F i) × M) ≃* F 0 × TailAmbient F M where
  toFun z := (z.1 0,((fun j => z.1 j.succ),z.2))
  invFun z := (Fin.cons z.1 z.2.1,z.2.2)
  left_inv z := by
    apply Prod.ext
    · funext i
      exact Fin.cases rfl (fun j => rfl) i
    · rfl
  right_inv z := rfl
  map_mul' _ _ := rfl

def splitImage (J : Family F M) :
    ActualPhysicalPeelPackets.Family (F 0) (TailAmbient F M) := by
  refine ⟨J.val.map (split F M).toMonoidHom,top_unique ?_⟩
  intro g hg
  obtain ⟨h,hh⟩ := J.property 0 g
  exact ⟨split F M h.val,⟨h.val,h.property,rfl⟩,hh⟩

theorem residual_full (J : Family F M) (i : Fin t) : Function.Surjective
    (fun h : ActualPhysicalPeelPackets.residual (F 0) (TailAmbient F M)
      (splitImage F M J) => h.val.1 i) := by
  intro g
  obtain ⟨h,hh⟩ := J.property i.succ g
  let z := split F M h.val
  have hz : z∈(splitImage F M J).val := ⟨h.val,h.property,rfl⟩
  exact ⟨⟨z.2,⟨z,hz,rfl⟩⟩,hh⟩

def Packet := Σ E : Family (TailFactors F) M,
  Σ N : ActualPhysicalPeelPackets.NormalMenu (F 0),
    letI : N.val.Normal := N.property
    ActualIsolatedFreeEpimorphism.Family ((F 0) ⧸ N.val) E.val

def code (J : Family F M) : Packet F M := by
  let p := ActualPhysicalPeelPackets.code (F 0) (TailAmbient F M) (splitImage F M J)
  exact ⟨⟨p.1,residual_full F M J⟩,p.2⟩

def forget (p : Packet F M) : ActualPhysicalPeelPackets.Packet (F 0) (TailAmbient F M) :=
  ⟨p.1.val,p.2⟩

theorem code_injective : Function.Injective (code F M) := by
  intro J K he
  have hp := congrArg (forget F M) he
  have hs := ActualPhysicalPeelPackets.code_injective (F 0) (TailAmbient F M) hp
  apply Subtype.ext
  apply Subgroup.map_injective (f := (split F M).toMonoidHom) (split F M).injective
  exact congrArg Subtype.val hs

instance packetFinite [∀ i,Finite (F i)] [Finite M] : Finite (Packet F M) := by
  unfold Packet
  infer_instance

theorem card_le_packets [∀ i,Finite (F i)] [Finite M] :
    Nat.card (Family F M)≤Nat.card (Packet F M) :=
  Nat.card_le_card_of_injective (code F M) (code_injective F M)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualFullPhysicalWordPeel
