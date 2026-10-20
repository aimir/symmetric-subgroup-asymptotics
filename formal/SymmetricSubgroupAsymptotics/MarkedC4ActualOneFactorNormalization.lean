import SymmetricSubgroupAsymptotics.MarkedC4ActualIsolatedFreeEpimorphism

/-! One physical peel with its ACTUAL isolated normal subgroup. This
normalizes just the removed factor and recovers the original subgroup;
the retained second group may contain all global markers and verticals. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualOneFactorNormalization

variable (G E : Type) [Group G] [Group E] (N : Subgroup G) [N.Normal]

def unmarked : G →* G × E where
  toFun g := (g,1)
  map_one' := rfl
  map_mul' _ _ := by simp

abbrev Family := {J : Subgroup (G × E) //
  J.map (MonoidHom.fst G E)=⊤ ∧ J.map (MonoidHom.snd G E)=⊤ ∧
    J.comap (unmarked G E)=N}

def quotientMap : (G × E) →* ((G ⧸ N) × E) :=
  (QuotientGroup.mk' N).prodMap (MonoidHom.id E)
def normalized (J : Family G E N) : Subgroup ((G ⧸ N) × E) := J.val.map (quotientMap G E N)

theorem kernel_le (J : Family G E N) : (quotientMap G E N).ker≤J.val := by
  intro z hz
  have he := MonoidHom.mem_ker.mp hz
  have hg : z.1∈N := (QuotientGroup.eq_one_iff (N := N) z.1).mp
    (congrArg (fun x : (G ⧸ N) × E => x.1) he)
  have hm : z.2=1 := congrArg (fun x : (G ⧸ N) × E => x.2) he
  have hj : (z.1,1)∈J.val := by
    change z.1∈J.val.comap (unmarked G E)
    rw [J.property.2.2]
    exact hg
  exact (show (z.1,1)=z from Prod.ext rfl hm.symm) ▸ hj

theorem recover (J : Family G E N) :
    (normalized G E N J).comap (quotientMap G E N)=J.val :=
  Subgroup.comap_map_eq_self (kernel_le G E N J)

theorem fullSecond (J : Family G E N) :
    (normalized G E N J).map (MonoidHom.snd (G ⧸ N) E)=⊤ := by
  apply top_unique
  intro e he
  have heJ : e∈J.val.map (MonoidHom.snd G E) := by rw [J.property.2.1]; trivial
  obtain ⟨z,hz,hze⟩ := heJ
  exact ⟨quotientMap G E N z,⟨z,hz,rfl⟩,hze⟩

theorem isolated (J : Family G E N) (q : G ⧸ N)
    (hq : (q,1)∈normalized G E N J) : q=1 := by
  obtain ⟨z,hz,he⟩ := hq
  have hm : z.2=1 := congrArg (fun x : (G ⧸ N) × E => x.2) he
  have hg : z.1∈N := by
    rw [← J.property.2.2]
    change (z.1,1)∈J.val
    exact (show z=(z.1,1) from Prod.ext rfl hm) ▸ hz
  have hqg : QuotientGroup.mk' N z.1=q := congrArg (fun x : (G ⧸ N) × E => x.1) he
  exact hqg.symm.trans ((QuotientGroup.eq_one_iff (N := N) z.1).mpr hg)

theorem fullFirst (J : Family G E N) :
    (normalized G E N J).map (MonoidHom.fst (G ⧸ N) E)=⊤ := by
  apply top_unique
  intro q hq
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N q
  have hg : g∈J.val.map (MonoidHom.fst G E) := by rw [J.property.1]; trivial
  obtain ⟨z,hz,hzg⟩ := hg
  exact ⟨quotientMap G E N z,⟨z,hz,rfl⟩,congrArg (QuotientGroup.mk' N) hzg⟩

def code (J : Family G E N) : ActualIsolatedFreeEpimorphism.Family (G ⧸ N) E :=
  ⟨⟨⟨normalized G E N J,fullSecond G E N J⟩,isolated G E N J⟩,fullFirst G E N J⟩

theorem code_injective : Function.Injective (code G E N) := by
  intro J K he
  apply Subtype.ext
  have hn := congrArg (fun U : ActualIsolatedFreeEpimorphism.Family (G ⧸ N) E =>
    U.val.val.val.comap (quotientMap G E N)) he
  exact (recover G E N J).symm.trans (hn.trans (recover G E N K))

theorem card_le_epimorphisms [Finite G] [Finite E] :
    Nat.card (Family G E N)≤Nat.card {f : E →* G ⧸ N // Function.Surjective f} := by
  exact (Nat.card_le_card_of_injective (code G E N) (code_injective G E N)).trans
    (ActualIsolatedFreeEpimorphism.card_le (G ⧸ N) E)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualOneFactorNormalization
