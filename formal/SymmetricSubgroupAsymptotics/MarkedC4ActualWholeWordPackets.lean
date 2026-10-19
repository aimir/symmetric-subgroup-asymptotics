import SymmetricSubgroupAsymptotics.MarkedC4ActualWholeWordNormalization

/-! Actual whole-word normalization packets with fixed ORIGINAL normal
menus. The source may have vertical marks. The marker remains one group;
all quotient factors retain their separately supplied original degrees. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualWholeWordPackets
open ActualFullPhysicalWordPeel

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
abbrev Menu := ∀ i : Fin t,{N : Subgroup (F i) // N.Normal}
instance menuFinite : Finite (Menu F) := inferInstance
local instance : Fintype (Menu F) := Fintype.ofFinite _
local instance (i : Fin t) : Fintype (F i) := Fintype.ofFinite _
local instance (i : Fin t) : Fintype (Subgroup (F i)) := Fintype.ofFinite _
local instance (i : Fin t) : Fintype {N : Subgroup (F i) // N.Normal} := Fintype.ofFinite _
local instance factorNormal (N : Menu F) (i : Fin t) : (N i).val.Normal := (N i).property
abbrev Factors (N : Menu F) (i : Fin t) := F i ⧸ (N i).val

variable (M : Type) [Group M]
def quotientMap (N : Menu F) : ((∀ i,F i) × M) →* ((∀ i,Factors F N i) × M) where
  toFun x := ((fun i => QuotientGroup.mk' (N i).val (x.1 i)),x.2)
  map_one' := by
    apply Prod.ext
    · funext i
      exact (QuotientGroup.mk' _).map_one
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · funext i
      exact (QuotientGroup.mk' _).map_mul _ _
    · rfl

abbrev NormalizedFamily (N : Menu F) := {J : Family (Factors F N) M //
  ∀ (i : Fin t) (q : Factors F N i),(Pi.mulSingle i q,1)∈J.val →q=1}
def Packet := Σ N : Menu F,NormalizedFamily F M N
instance packetFinite [Finite M] : Finite (Packet F M) := by unfold Packet; infer_instance

def actualMenu (J : Family F M) : Menu F := fun i =>
  ⟨ActualWholeWordNormalization.factor F M J i,inferInstance⟩
def code (J : Family F M) : Packet F M :=
  ⟨actualMenu F M J,
    ⟨⟨ActualWholeWordNormalization.normalized F M J,
      ActualWholeWordNormalization.physical_full F M J⟩,
      ActualWholeWordNormalization.isolated_eq_one F M J⟩⟩
def decode (p : Packet F M) : Subgroup ((∀ i,F i) × M) :=
  p.2.val.val.comap (quotientMap F M p.1)

theorem recover (J : Family F M) : decode F M (code F M J)=J.val := by
  change (ActualWholeWordNormalization.normalized F M J).comap
    (quotientMap F M (actualMenu F M J))=J.val
  have hm : quotientMap F M (actualMenu F M J)=
      ActualWholeWordNormalization.quotientMap F M J := by
    apply MonoidHom.ext
    intro x
    rfl
  rw [hm]
  exact ActualWholeWordNormalization.recover F M J
theorem code_injective : Function.Injective (code F M) := by
  intro J K he
  apply Subtype.ext
  exact (recover F M J).symm.trans ((congrArg (decode F M) he).trans (recover F M K))
theorem card_le_packets [Finite M] : Nat.card (Family F M)≤Nat.card (Packet F M) :=
  Nat.card_le_card_of_injective (code F M) (code_injective F M)

/-- Fixed original normal-menu cost, independent of the marking rank.
Across recursion use the stronger monotone-chain menu once, not this cost
at every depth. -/
theorem card_menu_le (K : ℕ) (hK : ∀ i,Nat.card (F i)≤K) : Nat.card (Menu F)≤2^(K*t) := by
  change Nat.card (∀ i : Fin t,{N : Subgroup (F i) // N.Normal})≤_
  rw [Nat.card_pi]
  calc
    _≤∏ _i : Fin t,2^K := by
      apply Finset.prod_le_prod'
      intro i hi
      have hsub := Nat.card_le_card_of_injective
        (fun N : {N : Subgroup (F i) // N.Normal} => N.val) Subtype.val_injective
      have hmenu : Nat.card (Subgroup (F i))≤2^K := by
        simpa only [Nat.card_eq_fintype_card] using
          ActualQuotientTableauMenus.subgroup_menu_le F K hK i
      exact hsub.trans hmenu
    _=(2^K)^t := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _=2^(K*t) := (pow_mul _ _ _).symm

end SymmetricSubgroupAsymptotics.MarkedC4.ActualWholeWordPackets
