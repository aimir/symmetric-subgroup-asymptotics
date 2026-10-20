import SymmetricSubgroupAsymptotics.MarkedC4RDTOriginalWordStructure
import SymmetricSubgroupAsymptotics.MarkedC4ActualOriginalWordPullback

/-! Maximal fully projecting tails are selected in the ORIGINAL physical
word. Their actual quotient tails remain fully projecting. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMaximalOriginalTail
open RDTOriginalWordStructure ActualOriginalWordPullback

theorem exists_maximal_tail {t : ℕ} (K : Fin t → Type) [∀ i,Group (K i)]
    (L : Subgroup (∀ i,K i)) : ∃ tail : Finset (Fin t),MaximalTail K L tail := by
  let candidates : Finset (Finset (Fin t)) :=
    Finset.univ.filter (fun S => Function.Surjective (tailProjection K L S))
  have hempty : Function.Surjective (tailProjection K L ∅) := by
    intro z
    refine ⟨1,?_⟩
    funext i
    exact False.elim (Finset.notMem_empty i.val i.property)
  have hnonempty : candidates.Nonempty :=
    ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hempty⟩⟩
  obtain ⟨tail,htail,hmax⟩ := Finset.exists_max_image candidates Finset.card hnonempty
  refine ⟨tail,(Finset.mem_filter.mp htail).2,?_⟩
  intro S hS
  exact hmax S (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS⟩)

theorem quotient_tail_surjective {t : ℕ} (K F : Fin t → Type)
    [∀ i,Group (K i)] [∀ i,Group (F i)]
    (q : ∀ i,K i →* F i) (onto : ∀ i,Function.Surjective (q i))
    (H : Subgroup (∀ i,F i)) (tail : Finset (Fin t))
    (hfull : Function.Surjective (tailProjection K (OriginalWord K F q H) tail)) :
    Function.Surjective (tailProjection F H tail) := by
  intro z
  let y : ∀ i : {j // j∈tail},K i.val := fun i =>
    Classical.choose (onto i.val (z i))
  obtain ⟨x,hx⟩ := hfull y
  refine ⟨quotientMap K F q H x,?_⟩
  funext i
  change q i.val (x.val i.val)=z i
  have hi : x.val i.val=y i := congrFun hx i
  rw [hi]
  exact Classical.choose_spec (onto i.val (z i))

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMaximalOriginalTail
