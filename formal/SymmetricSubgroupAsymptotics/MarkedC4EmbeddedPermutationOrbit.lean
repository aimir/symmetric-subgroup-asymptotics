import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-! Orbit cutoff is preserved when an actual permutation action is
embedded into a larger label alphabet and passed to its actual image. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.EmbeddedPermutationOrbit
variable {G A B : Type} [Group G] [MulAction G A] (ι : A ↪ B)

def action : G →* Equiv.Perm B :=
  (Equiv.Perm.viaEmbeddingHom ι).comp (MulAction.toPermHom G A)

private def orbitMap (x : A) : MulAction.orbit G x →
    MulAction.orbit (action (G := G) ι).range (ι x) := fun y =>
  ⟨ι y.1,by
    obtain ⟨g,hg⟩ := y.property
    refine ⟨⟨action (G := G) ι g,⟨g,rfl⟩⟩,?_⟩
    change (MulAction.toPermHom G A g).viaEmbedding ι (ι x)=ι y.1
    rw [Equiv.Perm.viaEmbedding_apply]
    exact congrArg ι hg⟩

def orbitEquiv (x : A) : MulAction.orbit G x ≃
    MulAction.orbit (action (G := G) ι).range (ι x) :=
  Equiv.ofBijective (orbitMap (G := G) ι x) ⟨by
    intro y z h
    apply Subtype.ext
    exact ι.injective (show ι y.val=ι z.val from
      congrArg (fun u : MulAction.orbit (action (G := G) ι).range (ι x) => u.val) h),by
    rintro ⟨y,hy⟩
    obtain ⟨h,hh⟩ := hy
    obtain ⟨g,hg⟩ := h.property
    refine ⟨⟨g • x,MulAction.mem_orbit x g⟩,Subtype.ext ?_⟩
    change ι (g • x)=y
    rw [← hh]
    change ι (g • x)=h.val (ι x)
    rw [← hg]
    exact (Equiv.Perm.viaEmbedding_apply (MulAction.toPermHom G A g) ι x).symm⟩

theorem orbit_card_image (x : A) :
    Nat.card (MulAction.orbit (action (G := G) ι).range (ι x))=Nat.card (MulAction.orbit G x) :=
  (Nat.card_congr (orbitEquiv (G := G) ι x)).symm

theorem orbit_card_outside (x : B) (hx : x∉Set.range ι) :
    Nat.card (MulAction.orbit (action (G := G) ι).range x)=1 := by
  have hf (y : MulAction.orbit (action (G := G) ι).range x) : (y : B)=x := by
    obtain ⟨h,hh⟩ := y.property
    obtain ⟨g,hg⟩ := h.property
    rw [← hh]
    change h.val x=x
    rw [← hg]
    exact Equiv.Perm.viaEmbedding_apply_of_notMem (MulAction.toPermHom G A g) ι x hx
  letI : Unique (MulAction.orbit (action (G := G) ι).range x) := {
    default := ⟨x,MulAction.mem_orbit_self x⟩
    uniq := fun y => Subtype.ext (hf y) }
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩

theorem cutoff {C : ℕ} (hC : 1<C)
    (horbit : ∀ x : A,Nat.card (MulAction.orbit G x)<C) :
    ∀ y : B,Nat.card (MulAction.orbit (action (G := G) ι).range y)<C := by
  intro y
  by_cases hy : y∈Set.range ι
  · obtain ⟨x,rfl⟩ := hy
    rw [orbit_card_image (G := G) ι]
    exact horbit x
  · rw [orbit_card_outside (G := G) ι y hy]
    exact hC
end SymmetricSubgroupAsymptotics.MarkedC4.EmbeddedPermutationOrbit
