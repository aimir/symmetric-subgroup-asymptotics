import SymmetricSubgroupAsymptotics.MarkedC4ActualFullPhysicalWordPeel
import SymmetricSubgroupAsymptotics.MarkedC4ActualOriginalWordPullback

/-! Fixed physical quotient maps with one SAME global marker. The actual
quotient source A determines its raw original source by comap, and maps
back onto A. Thus a fixed-history stage introduces no fresh normal menu. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedWordPullback
open ActualFullPhysicalWordPeel

variable {t : ℕ} (K F : Fin t → Type) [∀ i,Group (K i)] [∀ i,Group (F i)]
  (q : ∀ i,K i →* F i) (onto : ∀ i,Function.Surjective (q i))
  (M : Type) [Group M]

def ambientMap : ((∀ i,K i) × M) →* ((∀ i,F i) × M) :=
  (ActualOriginalWordPullback.productMap K F q).prodMap (MonoidHom.id M)

include onto in
theorem ambientMap_surjective : Function.Surjective (ambientMap K F q M) := by
  intro z
  let x : ∀ i,K i := fun i => Classical.choose (onto i (z.1 i))
  refine ⟨(x,z.2),Prod.ext ?_ rfl⟩
  funext i
  exact Classical.choose_spec (onto i (z.1 i))

def raw (A : Family F M) : Subgroup ((∀ i,K i) × M) :=
  A.val.comap (ambientMap K F q M)

include onto in
theorem raw_full (A : Family F M) (i : Fin t) :
    Function.Surjective (fun h : raw K F q M A => h.val.1 i) := by
  intro k
  obtain ⟨a,ha⟩ := A.property i (q i k)
  let x : ∀ j,K j := fun j => Classical.choose (onto j (a.val.1 j))
  let y := Function.update x i k
  have hy : ambientMap K F q M (y,a.val.2)=a.val := by
    apply Prod.ext
    · funext j
      by_cases hji : j=i
      · subst j
        change q i (Function.update x i k i)=a.val.1 i
        rw [Function.update_self]
        exact ha.symm
      · change q j (Function.update x i k j)=a.val.1 j
        rw [Function.update_of_ne hji]
        exact Classical.choose_spec (onto j (a.val.1 j))
    · rfl
  refine ⟨⟨(y,a.val.2),show ambientMap K F q M (y,a.val.2)∈A.val from hy.symm ▸ a.property⟩,?_⟩
  exact Function.update_self i k x

include onto in
def code (A : Family F M) : Family K M :=
  ⟨raw K F q M A,raw_full K F q onto M A⟩

include onto in
theorem recover (A : Family F M) :
    (raw K F q M A).map (ambientMap K F q M)=A.val := by
  apply Subgroup.map_comap_eq_self
  rw [(ambientMap K F q M).range_eq_top_of_surjective
    (ambientMap_surjective K F q onto M)]
  exact le_top

include onto in
theorem code_injective : Function.Injective (code K F q onto M) := by
  intro A B he
  apply Subtype.ext
  have hr := congrArg (fun E : Family K M => E.val.map (ambientMap K F q M)) he
  exact (recover K F q onto M A).symm.trans (hr.trans (recover K F q onto M B))

include onto in
theorem card_le_raw [∀ i,Finite (K i)] [Finite M] :
    Nat.card (Family F M)≤Nat.card (Family K M) :=
  Nat.card_le_card_of_injective (code K F q onto M) (code_injective K F q onto M)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedWordPullback
