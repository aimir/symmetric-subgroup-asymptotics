import SymmetricSubgroupAsymptotics.TernaryFullWeightReindex

/-! The two smallest full-coordinate ternary factors. On an empty or
one-point coordinate set, every full-coordinate subspace is the whole
space, so its exact weighted factor is one. No finite subgroup enumeration
or supplied numerical witness is used. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.TernaryFullFactorSmall

open DiagonalInvariantSubmodules DiagonalFullSubmoduleEquiv DiagonalFullSubmoduleWeights
open TernaryFullWeightReindex

variable {k I : Type*} [Field k] [Subsingleton I]

theorem full_eq_top (K : Submodule k (I → k)) (hK : FullCoordinates K) : K=⊤ := by
  apply top_unique
  intro v _
  by_cases hi : Nonempty I
  · let i : I := Classical.choice hi
    obtain ⟨w,hw⟩ := hK i (v i)
    have he : w.1=v := by
      funext j
      have hj : j=i := Subsingleton.elim _ _
      rw [hj]
      exact hw
    exact he ▸ w.2
  · have hzero : v=0 := by
      funext i
      exact False.elim (hi ⟨i⟩)
    rw [hzero]
    exact K.zero_mem

def topFull : FullSubmodule (k := k) I := ⟨⊤,by
  intro i c
  exact ⟨⟨fun _ => c,Submodule.mem_top⟩,rfl⟩⟩

attribute [local instance] Fintype.ofFinite

theorem weight_eq_one [Fintype I] : ternaryFullWeight I=1 := by
  letI : Finite (FullSubmodule (k := ZMod 3) I) :=
    Finite.of_injective
      (fun K : FullSubmodule (k := ZMod 3) I => (K.1 : Set (I → ZMod 3)))
      (fun _ _ h => Subtype.ext (SetLike.coe_injective h))
  unfold ternaryFullWeight
  calc
    _ = (3 : ℕ)^(Fintype.card I -
        Module.finrank (ZMod 3) (⊤ : Submodule (ZMod 3) (I → ZMod 3))) := by
      apply Finset.sum_eq_single (topFull : FullSubmodule (k := ZMod 3) I)
      · intro K _ hK
        exact False.elim (hK (Subtype.ext (full_eq_top K.1 K.2)))
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    _ = 1 := by rw [finrank_top]; simp

@[simp] theorem factor_zero : ternaryFullFactor 0=1 :=
  weight_eq_one (I := Fin 0)

@[simp] theorem factor_one : ternaryFullFactor 1=1 :=
  weight_eq_one (I := Fin 1)

end SymmetricSubgroupAsymptotics.TernaryFullFactorSmall

end
