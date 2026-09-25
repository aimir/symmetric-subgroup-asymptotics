import SymmetricSubgroupAsymptotics.BinaryPairFixedCertificates
import SymmetricSubgroupAsymptotics.BinaryPairSection
import Mathlib.GroupTheory.Index

/-! Fixed-space dimensions from cardinalities of original group fibres.
This avoids assuming a capacity or replacing a quotient section by an
unrelated vector-space action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod p) V]

def sectionSubspacePreimage (q : K →* Multiplicative V) (W : Submodule (ZMod p) V) :
    Subgroup K := W.toAddSubgroup.toSubgroup.comap q

def sectionSubspaceMap (q : K →* Multiplicative V) (W : Submodule (ZMod p) V) :
    sectionSubspacePreimage q W →* Multiplicative W where
  toFun k := Multiplicative.ofAdd ⟨(q (k:K)).toAdd,k.2⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd q.map_one
  map_mul' a b := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (q.map_mul (a:K) (b:K))

theorem sectionSubspaceMap_surjective (q : K →* Multiplicative V)
    (hq : Function.Surjective q) (W : Submodule (ZMod p) V) :
    Function.Surjective (sectionSubspaceMap q W) := by
  intro v
  obtain ⟨k,hk⟩ := hq (Multiplicative.ofAdd v.toAdd.val)
  have hm : k∈sectionSubspacePreimage q W := by
    change (q k).toAdd∈W
    rw [hk]
    exact v.toAdd.property
  refine ⟨⟨k,hm⟩,?_⟩
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd hk

def sectionSubspaceMapKernelEquiv (q : K →* Multiplicative V)
    (W : Submodule (ZMod p) V) : (sectionSubspaceMap q W).ker ≃* q.ker where
  toFun k := ⟨((k.1:sectionSubspacePreimage q W):K),by
    have he := congrArg (fun v : Multiplicative W => v.toAdd.val) k.2
    change (q (k.1:K)).toAdd=0 at he
    exact congrArg Multiplicative.ofAdd he⟩
  invFun k := ⟨⟨(k:K),by
    change (q (k:K)).toAdd∈W
    rw [show q (k:K)=1 from k.2]
    exact W.zero_mem⟩,by
      apply congrArg Multiplicative.ofAdd
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd k.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem sectionSubspacePreimage_card (q : K →* Multiplicative V)
    (hq : Function.Surjective q) (W : Submodule (ZMod p) V) :
    Nat.card (sectionSubspacePreimage q W)=Nat.card q.ker*Nat.card W := by
  have h := (sectionSubspaceMap q W).ker.card_mul_index
  rw [Subgroup.index_ker] at h
  have hk := Nat.card_congr (sectionSubspaceMapKernelEquiv q W).toEquiv
  have hr : Nat.card (sectionSubspaceMap q W).range=Nat.card W := by
    rw [MonoidHom.range_eq_top.mpr (sectionSubspaceMap_surjective q hq W)]
    exact Nat.card_congr (Equiv.Set.univ _ |>.trans Multiplicative.toAdd)
  rw [hk,hr] at h
  exact h.symm

theorem sectionFixedPreimage_mem_iff {G : Type*} [Group G]
    (q : K →* Multiplicative V) (ρ : Representation (ZMod p) G V)
    (α : G →* MulAut K)
    (heq : ∀ g k, ρ g (q k).toAdd=(q (α g k)).toAdd) (k : K) :
    k∈sectionSubspacePreimage q ρ.invariants ↔ ∀ g, k⁻¹*α g k∈q.ker := by
  change (∀ g, ρ g (q k).toAdd=(q k).toAdd) ↔ _
  constructor
  · intro h g
    apply (MonoidHom.eq_iff q).mp
    apply Multiplicative.toAdd.injective
    exact (heq g k).symm.trans (h g)
  · intro h g
    rw [heq]
    exact congrArg Multiplicative.toAdd ((MonoidHom.eq_iff q).mpr (h g))

section Capacity
variable {G K₀ V₀ : Type} [Group G] [Group K₀]
    [AddCommGroup V₀] [Module (ZMod 2) V₀] [Finite K₀] [Finite V₀]

/-- Two checked original subgroup orders determine the actual invariant
dimension, hence the Schur capacity. -/
theorem binary_section_capacity_of_card
    (q : K₀ →* Multiplicative V₀) (hq : Function.Surjective q)
    (ρ : Representation (ZMod 2) G V₀) (hG : IsPGroup 2 G) (r : ℕ)
    (hcard : Nat.card (sectionSubspacePreimage q ρ.invariants)=Nat.card q.ker*2^r) :
    representationSchurCapacity ρ=(r:ℝ) := by
  rw [pGroup_representationSchurCapacity hG ρ]
  have hc := sectionSubspacePreimage_card q hq ρ.invariants
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ρ.invariants),
    Nat.card_eq_fintype_card (α := ZMod 2),ZMod.card] at hc
  have he : 2^Module.finrank (ZMod 2) ρ.invariants=2^r :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hc.symm.trans hcard)
  have hd := (Nat.pow_right_injective (by decide : 1<2)) he
  exact congrArg (Nat.cast : ℕ→ℝ) hd

end Capacity
end SymmetricSubgroupAsymptotics
