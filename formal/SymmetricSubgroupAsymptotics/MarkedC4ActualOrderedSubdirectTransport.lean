import SymmetricSubgroupAsymptotics.MarkedC4ActualSelectedOrderPrefix
import SymmetricSubgroupAsymptotics.MarkedC4ActualSubdirectFiltration

/-! Actual subdirect transport along a selected order of ORIGINAL labels.
The new group is the literal coordinate-reindexed image. Its prefix and
diagonal entries are identified with the original residual image entries. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualOrderedSubdirectTransport
open ActualSelectedOrderPrefix

variable {I : Type} [Fintype I] [DecidableEq I] {t : ℕ}
  (e : Fin t ≃ I) (F : I → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i))

abbrev Factors := fun k : Fin t => F (e k)
def physicalEquiv : (∀ i,F i) ≃* (∀ k,Factors e F k) where
  toEquiv := (Equiv.piCongrLeft F e).symm
  map_mul' v w := by funext k; rfl

def image : Subgroup (∀ k,Factors e F k) := H.map (physicalEquiv e F).toMonoidHom
def sourceEquiv : H ≃* image e F H :=
  H.equivMapOfInjective (physicalEquiv e F).toMonoidHom (physicalEquiv e F).injective

theorem sourceEquiv_coordinate (h : H) (k : Fin t) :
    (sourceEquiv e F H h).val k=h.val (e k) := rfl

/-- Literal physical subdirectness survives the selected original order. -/
theorem subdirect (hH : ∀ i,Function.Surjective (ActualTableauPeeling.coordinate F H i))
    (k : Fin t) : Function.Surjective
      (ActualSubdirectFiltration.coordinate (Factors e F) (image e F H) k) := by
  intro q
  obtain ⟨h,hh⟩ := hH (e k) q
  exact ⟨sourceEquiv e F H h,hh⟩

/-- Actual ordered prefix kernels are transported, not replaced by kernels
of unrelated quotient actions. -/
theorem prefix_comap (m : ℕ) :
    (ActualSubdirectFiltration.«prefix» (Factors e F) (image e F H) m).comap
      (sourceEquiv e F H).toMonoidHom=orderedPrefix e F H m := by
  ext h
  rw [Subgroup.mem_comap,ActualSubdirectFiltration.mem_prefix,mem_orderedPrefix]
  rfl

theorem prefix_map (m : ℕ) :
    (orderedPrefix e F H m).map (sourceEquiv e F H).toMonoidHom=
      ActualSubdirectFiltration.«prefix» (Factors e F) (image e F H) m := by
  rw [← prefix_comap]
  apply Subgroup.map_comap_eq_self
  rw [(sourceEquiv e F H).toMonoidHom.range_eq_top_of_surjective
    (sourceEquiv e F H).surjective]
  exact le_top

/-- The SAME actual diagonal appears in the original residual tableau. -/
theorem diagonal_eq_entry (k : Fin t) :
    ActualSubdirectFiltration.diagonal (Factors e F) (image e F H) k=
      ActualTableauPeeling.entry F H (initialLabels e (k.val+1)) (e k) := by
  unfold ActualSubdirectFiltration.diagonal
  rw [← prefix_map,Subgroup.map_map]
  have hc :
      (ActualSubdirectFiltration.coordinate (Factors e F) (image e F H) k).comp
        (sourceEquiv e F H).toMonoidHom=ActualTableauPeeling.coordinate F H (e k) := by
    apply MonoidHom.ext
    intro h
    rfl
  rw [hc,ordered_entry]

/-- All original marked Hom weights are preserved by this actual reorder. -/
def homEquiv {M : Type} [Group M] : (H →* M) ≃ (image e F H →* M) where
  toFun f := f.comp (sourceEquiv e F H).symm.toMonoidHom
  invFun f := f.comp (sourceEquiv e F H).toMonoidHom
  left_inv f := by ext h; simp
  right_inv f := by ext h; simp

theorem hom_card_eq {M : Type} [Group M] : Nat.card (H →* M)=
    Nat.card (image e F H →* M) := Nat.card_congr (homEquiv e F H)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualOrderedSubdirectTransport
