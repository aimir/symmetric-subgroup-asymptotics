import SymmetricSubgroupAsymptotics.MarkedC4ActualOneFactorNormalization
import SymmetricSubgroupAsymptotics.MarkedC4ActualProjectionHallFibre

/-! Actual global one-factor peel partition: retained second subgroup,
actual isolated normal subgroup in the removed original factor, and an
actual isolated-free epimorphism fibre. Every original subgroup is recovered. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualPhysicalPeelPackets

variable (G B : Type) [Group G] [Group B]
abbrev Family := {J : Subgroup (G × B) // J.map (MonoidHom.fst G B)=⊤}
abbrev NormalMenu := {N : Subgroup G // N.Normal}

def residual (J : Family G B) : Subgroup B := J.val.map (MonoidHom.snd G B)

theorem first_surjective (J : Family G B) :
    Function.Surjective (Prod.fst ∘ J.val.subtype) := by
  intro g
  have hg : g∈J.val.map (MonoidHom.fst G B) := by rw [J.property]; trivial
  obtain ⟨z,hz,hzg⟩ := hg
  exact ⟨⟨z,hz⟩,hzg⟩

def actualNormal (J : Family G B) : NormalMenu G :=
  ⟨J.val.goursatFst,Subgroup.normal_goursatFst (first_surjective G B J)⟩

def restricted (J : Family G B) :
    AbelianProductGraphClassification.FullSecond G (residual G B J) :=
  ActualProjectionHallFibre.code (residual G B J) ⟨J.val,rfl⟩

def actualStage (J : Family G B) :
    ActualOneFactorNormalization.Family G (residual G B J) (actualNormal G B J).val := by
  refine ⟨(restricted G B J).val,?_,(restricted G B J).property,?_⟩
  · apply top_unique
    intro g hg
    have hgj : g∈J.val.map (MonoidHom.fst G B) := by rw [J.property]; trivial
    obtain ⟨z,hz,hzg⟩ := hgj
    let e : residual G B J := ⟨z.2,⟨z,hz,rfl⟩⟩
    exact ⟨(z.1,e),hz,hzg⟩
  · ext g
    change (g,1)∈J.val ↔ g∈J.val.goursatFst
    exact Subgroup.mem_goursatFst.symm

def Packet := Σ E : Subgroup B,Σ N : NormalMenu G,
  letI : N.val.Normal := N.property
  ActualIsolatedFreeEpimorphism.Family (G ⧸ N.val) E

def code (J : Family G B) : Packet G B := by
  letI : (actualNormal G B J).val.Normal := (actualNormal G B J).property
  exact ⟨residual G B J,actualNormal G B J,
    ActualOneFactorNormalization.code G (residual G B J) (actualNormal G B J).val
      (actualStage G B J)⟩

def decode (p : Packet G B) : Subgroup (G × B) := by
  letI : p.2.1.val.Normal := p.2.1.property
  exact (p.2.2.val.val.val.comap
    (ActualOneFactorNormalization.quotientMap G p.1 p.2.1.val)).map
      (ActualProjectionHallFibre.inclusion p.1)

theorem recover (J : Family G B) : decode G B (code G B J)=J.val := by
  letI : (actualNormal G B J).val.Normal := (actualNormal G B J).property
  change ((ActualOneFactorNormalization.normalized G (residual G B J)
    (actualNormal G B J).val (actualStage G B J)).comap
      (ActualOneFactorNormalization.quotientMap G (residual G B J) (actualNormal G B J).val)).map
        (ActualProjectionHallFibre.inclusion (residual G B J))=J.val
  rw [ActualOneFactorNormalization.recover]
  exact ActualProjectionHallFibre.recover (residual G B J) ⟨J.val,rfl⟩

theorem code_injective : Function.Injective (code G B) := by
  intro J K he
  apply Subtype.ext
  exact (recover G B J).symm.trans ((congrArg (decode G B) he).trans (recover G B K))

instance packetFinite [Finite G] [Finite B] : Finite (Packet G B) := by
  unfold Packet
  infer_instance

theorem card_le_packets [Finite G] [Finite B] : Nat.card (Family G B)≤Nat.card (Packet G B) :=
  Nat.card_le_card_of_injective (code G B) (code_injective G B)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualPhysicalPeelPackets
