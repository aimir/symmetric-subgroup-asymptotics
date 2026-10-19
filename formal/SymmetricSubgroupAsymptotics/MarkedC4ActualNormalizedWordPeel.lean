import SymmetricSubgroupAsymptotics.MarkedC4ActualWholeWordPackets

/-! Peel a fixed NORMALIZED physical word without creating another normal
menu. The retained source is its actual residual projection, with the SAME
mark group. The isolated-free fibre is an actual epi family of that source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalizedWordPeel
open ActualFullPhysicalWordPeel

variable {t : ℕ} (F : Fin (t+1) → Type) [∀ i,Group (F i)]
  (M : Type) [Group M]
abbrev Family := {J : ActualFullPhysicalWordPeel.Family F M //
  ∀ i g,(Pi.mulSingle i g,1)∈J.val →g=1}

def stage (J : Family F M) := splitImage F M J.val
abbrev Source (J : Family F M) :=
  ActualPhysicalPeelPackets.residual (F 0) (TailAmbient F M) (stage F M J)

def fibre (J : Family F M) :
    ActualIsolatedFreeEpimorphism.Family (F 0) (Source F M J) := by
  let s := stage F M J
  refine ⟨⟨ActualPhysicalPeelPackets.restricted (F 0) (TailAmbient F M) s,?_⟩,
    (ActualPhysicalPeelPackets.actualStage (F 0) (TailAmbient F M) s).property.1⟩
  intro g hg
  have hx : (g,1)∈s.val := hg
  obtain ⟨z,hz,he⟩ := hx
  have hfirst : z.1 0=g := congrArg (fun w : (F 0) × TailAmbient F M => w.1) he
  have htail : (fun j : Fin t => z.1 j.succ)=1 :=
    congrArg (fun w : (F 0) × TailAmbient F M => w.2.1) he
  have hmark : z.2=1 := congrArg (fun w : (F 0) × TailAmbient F M => w.2.2) he
  have hzsingle : z=(Pi.mulSingle 0 g,1) := by
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Pi.mulSingle_eq_same] using hfirst
      · have hj := congrFun htail j
        simpa [Pi.mulSingle] using hj
    · exact hmark
  exact J.property 0 g (hzsingle ▸ hz)

def Packet := Σ E : ActualFullPhysicalWordPeel.Family (TailFactors F) M,
  ActualIsolatedFreeEpimorphism.Family (F 0) E.val

def code (J : Family F M) : Packet F M :=
  ⟨⟨Source F M J,residual_full F M J.val⟩,fibre F M J⟩

def decode (p : Packet F M) : Subgroup ((∀ i,F i) × M) :=
  (p.2.val.val.val.map (ActualProjectionHallFibre.inclusion p.1.val)).map
    (split F M).symm.toMonoidHom

theorem recover (J : Family F M) : decode F M (code F M J)=J.val.val := by
  unfold decode code fibre
  change ((ActualPhysicalPeelPackets.restricted (F 0) (TailAmbient F M)
    (stage F M J)).val.map
      (ActualProjectionHallFibre.inclusion (Source F M J))).map
        (split F M).symm.toMonoidHom=J.val.val
  unfold ActualPhysicalPeelPackets.restricted
  rw [ActualProjectionHallFibre.recover]
  change (J.val.val.map (split F M).toMonoidHom).map
    (split F M).symm.toMonoidHom=J.val.val
  rw [Subgroup.map_map]
  have hc : (split F M).symm.toMonoidHom.comp (split F M).toMonoidHom=
      MonoidHom.id ((∀ i,F i) × M) := by
    apply MonoidHom.ext
    intro x
    exact (split F M).symm_apply_apply x
  rw [hc,Subgroup.map_id]

theorem code_injective : Function.Injective (code F M) := by
  intro J K he
  apply Subtype.ext
  apply Subtype.ext
  exact (recover F M J).symm.trans
    ((congrArg (decode F M) he).trans (recover F M K))

instance packetFinite [∀ i,Finite (F i)] [Finite M] : Finite (Packet F M) := by
  unfold Packet
  infer_instance

theorem card_le_packets [∀ i,Finite (F i)] [Finite M] :
    Nat.card (Family F M)≤Nat.card (Packet F M) :=
  Nat.card_le_card_of_injective (code F M) (code_injective F M)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalizedWordPeel
