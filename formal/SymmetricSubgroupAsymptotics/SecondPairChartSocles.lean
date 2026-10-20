import SymmetricSubgroupAsymptotics.NestedBinaryPairSocles

/-! A shared second physical pair chart for three-quartet actions.
Only the original point images need literal certificates. The inner
three-pair action and two possible six-cycle words are checked once. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SecondPairChartSocles

def outerFrame : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := if p.2 = 0 then ![0,3,1,4,2,5] p.1 else ![6,9,7,10,8,11] p.1
  invFun x := (![0,2,4,1,3,5,0,2,4,1,3,5] x,
    ![0,0,0,0,0,0,1,1,1,1,1,1] x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def innerFrame : Fin 3 × ZMod 2 ≃ Fin 6 where
  toFun p := if p.2 = 0 then ![0,2,4] p.1 else ![1,3,5] p.1
  invFun x := (![0,0,1,1,2,2] x,![0,1,0,1,0,1] x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r : Equiv.Perm (Fin 6) where
  toFun := ![3,2,5,4,0,1]
  invFun := ![4,5,1,0,3,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def s : Equiv.Perm (Fin 6) where
  toFun := ![3,2,1,0,4,5]
  invFun := ![3,2,1,0,4,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def f : Equiv.Perm (Fin 6) := Equiv.swap 4 5

def z : Equiv.Perm (Fin 6) where
  toFun := ![1,0,3,2,5,4]
  invFun := ![1,0,3,2,5,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairImage : Fin 5 → Equiv.Perm (Fin 6) := ![1,r,s,f,z]
def blockImage : Fin 5 → Equiv.Perm (Fin 3) :=
  ![1,NestedBinaryPairSocles.rotation,NestedBinaryPairSocles.reflection,1,1]

theorem inner_preserves : ∀ i,
    BinaryPairFrame.Preserves innerFrame (pairImage i) (blockImage i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem f_cycle_cover (i : Fin 6) : ∃ n : ℕ, ((f*r)^n) 0 = i := by
  refine ⟨(![0,3,4,1,5,2] : Fin 6 → ℕ) i,?_⟩
  revert i
  decide +kernel

theorem z_cycle_cover (i : Fin 6) : ∃ n : ℕ, ((z*r)^n) 0 = i := by
  refine ⟨(![0,3,1,4,2,5] : Fin 6 → ℕ) i,?_⟩
  revert i
  decide +kernel

theorem blockImage_cyclic {i : Fin 5} (hi : i ≠ 2) :
    blockImage i ∈ Subgroup.zpowers NestedBinaryPairSocles.rotation := by
  fin_cases i
  · exact (Subgroup.zpowers _).one_mem
  · exact Subgroup.mem_zpowers _
  · exact False.elim (hi rfl)
  · exact (Subgroup.zpowers _).one_mem
  · exact (Subgroup.zpowers _).one_mem

theorem quotientSocle_of_codes {ι : Type*}
    (generators : ι → Equiv.Perm (Fin 12)) (codes : ι → Fin 5)
    (hp : ∀ i, BinaryPairFrame.Preserves outerFrame (generators i) (pairImage (codes i)))
    (ci ri : ι) (hc : codes ci = 3 ∨ codes ci = 4) (hr : codes ri = 1)
    (hs : (∃ si, codes si = 2) ∨ (∀ i, codes i ≠ 2))
    (N : Subgroup (Subgroup.closure (Set.range generators))) [N.Normal] :
    SocleNormalGeneratorBound ((Subgroup.closure (Set.range generators)) ⧸ N) 3 := by
  apply NestedBinaryPairSocles.quotientSocle_of_generators outerFrame innerFrame generators
    (fun i => pairImage (codes i)) (fun i => blockImage (codes i)) hp
    (fun i => inner_preserves (codes i)) ci ri ri ?_ ?_ ?_ N
  · change blockImage (codes ri) = NestedBinaryPairSocles.rotation
    rw [hr]
    rfl
  · rcases hs with ⟨si,hsi⟩ | hcyclic
    · exact Or.inl ⟨si,by
        change blockImage (codes si) = NestedBinaryPairSocles.reflection
        rw [hsi]
        rfl⟩
    · exact Or.inr (fun i => blockImage_cyclic (hcyclic i))
  · intro i
    change ∃ n : ℕ, ((pairImage (codes ci) * pairImage (codes ri)) ^ n) 0 = i
    rw [hr]
    rcases hc with hc | hc
    · rw [hc]
      exact f_cycle_cover i
    · rw [hc]
      exact z_cycle_cover i

end SymmetricSubgroupAsymptotics.SecondPairChartSocles

end
