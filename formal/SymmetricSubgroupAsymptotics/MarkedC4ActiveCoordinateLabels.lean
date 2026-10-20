import SymmetricSubgroupAsymptotics.MarkedC4PhysicalGridLabels
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! Sentinel-preserving permutation actions on the finite original-label
alphabet. Equivariance is proved from the constructed compressed action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActiveCoordinateLabels
open PhysicalGridLabels
variable {I : Type} [Fintype I] (F : I → Type) [∀ i, Fintype (F i)]
  {b : ℕ} (hcard : Fintype.card (Active F)≤b)

local instance : Fintype (Active F) := Fintype.ofFinite _
def embedding : Active F ↪ Fin (b+1) where
  toFun z := ⟨(Fintype.equivFin (Active F) z).val+1,by
    have := (Fintype.equivFin (Active F) z).isLt; omega⟩
  inj' := by
    intro z w h
    apply (Fintype.equivFin (Active F)).injective
    apply Fin.ext
    have hv := congrArg Fin.val h
    exact Nat.add_right_cancel hv

def label (i : I) (x : F i) : Fin (b+1) :=
  if hi : Nat.card (F i)=1 then 0 else embedding F hcard ⟨i,⟨x,hi⟩⟩

theorem label_val (i : I) (x : F i) :
    (label F hcard i x).val=activeLabel F i x := by
  by_cases hi : Nat.card (F i)=1
  · simp only [label,activeLabel,dif_pos hi]
    rfl
  · simp only [label,activeLabel,dif_neg hi]
    rfl

variable {G : Type} [Group G] [∀ i, MulAction G (F i)]
def action : G →* Equiv.Perm (Fin (b+1)) :=
  (Equiv.Perm.viaEmbeddingHom (embedding F hcard)).comp
    (ActiveFiberPermutation.action F)

theorem equivariant (g : G) (i : I) (x : F i) :
    label F hcard i (g • x)=action F hcard g (label F hcard i x) := by
  by_cases hi : Nat.card (F i)=1
  · simp only [label,dif_pos hi]
    symm
    apply Equiv.Perm.viaEmbedding_apply_of_notMem
    rintro ⟨z,hz⟩
    have hv := congrArg Fin.val hz
    change (Fintype.equivFin (Active F) z).val+1=0 at hv
    omega
  · simp only [label,dif_neg hi]
    change embedding F hcard ⟨i,⟨g • x,hi⟩⟩=
      (ActiveFiberPermutation.action F g).viaEmbedding (embedding F hcard)
        (embedding F hcard ⟨i,⟨x,hi⟩⟩)
    rw [Equiv.Perm.viaEmbedding_apply]
    rfl
end SymmetricSubgroupAsymptotics.MarkedC4.ActiveCoordinateLabels
