import SymmetricSubgroupAsymptotics.MarkedC4ActualSubdirectFiltration

/-! Quotient physical words are pulled back to their ORIGINAL physical
factors, retaining original actions/degrees before any ordinary RDT5.5 use. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalWordPullback
open ActualSubdirectFiltration

variable {t : ℕ} (K F : Fin t → Type) [∀ i,Group (K i)] [∀ i,Group (F i)]
  (q : ∀ i,K i →* F i) (onto : ∀ i,Function.Surjective (q i))
  (H : Subgroup (∀ i,F i))

def productMap : (∀ i,K i) →* (∀ i,F i) where
  toFun x i := q i (x i)
  map_one' := by funext i; exact (q i).map_one
  map_mul' x y := by funext i; exact (q i).map_mul (x i) (y i)

def OriginalWord : Subgroup (∀ i,K i) := H.comap (productMap K F q)
def quotientMap : OriginalWord K F q H →* H where
  toFun x := ⟨productMap K F q x.val,x.property⟩
  map_one' := by apply Subtype.ext; exact (productMap K F q).map_one
  map_mul' x y := by apply Subtype.ext; exact (productMap K F q).map_mul x.val y.val

include onto in
theorem quotientMap_surjective : Function.Surjective (quotientMap K F q H) := by
  intro h
  let x : ∀ i,K i := fun i => Classical.choose (onto i (h.val i))
  have hx : productMap K F q x=h.val := by
    funext i
    exact Classical.choose_spec (onto i (h.val i))
  exact ⟨⟨x,show productMap K F q x∈H from hx.symm ▸ h.property⟩,Subtype.ext hx⟩

include onto in
/-- Actual quotient subdirectness pulls back to ORIGINAL transitive
factors. No transitive action on the quotient factors is introduced. -/
theorem original_subdirect (hfull : ∀ i,Function.Surjective (coordinate F H i))
    (i : Fin t) : Function.Surjective (coordinate K (OriginalWord K F q H) i) := by
  intro k
  obtain ⟨h,hh⟩ := hfull i (q i k)
  let x : ∀ j,K j := fun j => Classical.choose (onto j (h.val j))
  let y := Function.update x i k
  have hy : productMap K F q y=h.val := by
    funext j
    by_cases hji : j=i
    · subst j
      change q i (Function.update x i k i)=h.val i
      rw [Function.update_self]
      exact hh.symm
    · change q j (Function.update x i k j)=h.val j
      rw [Function.update_of_ne hji]
      exact Classical.choose_spec (onto j (h.val j))
  refine ⟨⟨y,show productMap K F q y∈H from hy.symm ▸ h.property⟩,?_⟩
  change Function.update x i k i=k
  exact Function.update_self i k x

end SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalWordPullback
