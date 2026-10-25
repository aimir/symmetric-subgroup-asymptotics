import SymmetricSubgroupAsymptotics.SubgroupActionIntersectionTransport
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateDisjoint
import Mathlib.GroupTheory.Sylow

/-! Ordered Sylow pairs can be conjugated in the FULL ambient group.
Disjoint restrictions to a normal subgroup are first upgraded using a
proved standard-position criterion. The pair itself, not an automorphism
of the normal subgroup, is transported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.NormalSylowAmbientPairAlignment
open SubgroupActionIntersectionTransport
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem ambient_intersection_bot_of_normal_restrictions
    (N : Subgroup G) [N.Normal] (U R S : Sylow p G)
    (hcriterion : ∀ g : G,
      (U : Subgroup G).comap N.subtype ⊓
        ((U : Subgroup G).comap N.subtype).map (MulAut.conjNormal g).toMonoidHom = ⊥ →
      (U : Subgroup G) ⊓ (U : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊥)
    (hRS : (R : Subgroup G).comap N.subtype ⊓ (S : Subgroup G).comap N.subtype = ⊥) :
    (R : Subgroup G) ⊓ (S : Subgroup G) = ⊥ := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G R U
  let T : Sylow p G := a • S
  have hR : (R : Subgroup G).map (MulAut.conj a).toMonoidHom = (U : Subgroup G) :=
    congrArg (fun P : Sylow p G => (P : Subgroup G)) ha
  have hS : (S : Subgroup G).map (MulAut.conj a).toMonoidHom = (T : Subgroup G) := rfl
  have hN : (U : Subgroup G).comap N.subtype ⊓ (T : Subgroup G).comap N.subtype = ⊥ := by
    have hh := congrArg (fun P : Subgroup N => P.map (MulAut.conjNormal a).toMonoidHom) hRS
    dsimp only at hh
    rw [Subgroup.map_inf _ _ (MulAut.conjNormal a).toMonoidHom
      (MulAut.conjNormal a).injective, Subgroup.map_bot] at hh
    rw [← normal_comap_conjugate N (R : Subgroup G) a,
      ← normal_comap_conjugate N (S : Subgroup G) a, hR, hS] at hh
    exact hh
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G U T
  have hkmap : (U : Subgroup G).map (MulAut.conj k).toMonoidHom = (T : Subgroup G) :=
    congrArg (fun P : Sylow p G => (P : Subgroup G)) hk
  have hNk : (U : Subgroup G).comap N.subtype ⊓
      ((U : Subgroup G).comap N.subtype).map (MulAut.conjNormal k).toMonoidHom = ⊥ := by
    rw [← normal_comap_conjugate N (U : Subgroup G) k, hkmap]
    exact hN
  have hUT : (U : Subgroup G) ⊓ (T : Subgroup G) = ⊥ := by
    have hh := hcriterion k hNk
    rwa [hkmap] at hh
  apply Subgroup.map_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective
  rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective, Subgroup.map_bot, hR, hS]
  exact hUT

theorem exists_conj_pair (P Q R S : Sylow p G)
    (hRS : (R : Subgroup G) ⊓ (S : Subgroup G) = ⊥)
    (halign : ∀ g : G,
      (P : Subgroup G) ⊓ (P : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊥ →
      ∃ b ∈ Subgroup.normalizer (P : Set G),
        (P : Subgroup G).map (MulAut.conj g).toMonoidHom =
          (Q : Subgroup G).map (MulAut.conj b).toMonoidHom) :
    ∃ g : G, g • R = P ∧ g • S = Q := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G R P
  let T : Sylow p G := a • S
  have hR : (R : Subgroup G).map (MulAut.conj a).toMonoidHom = (P : Subgroup G) :=
    congrArg (fun U : Sylow p G => (U : Subgroup G)) ha
  have hS : (S : Subgroup G).map (MulAut.conj a).toMonoidHom = (T : Subgroup G) := rfl
  have hPT : (P : Subgroup G) ⊓ (T : Subgroup G) = ⊥ := by
    have hh := congrArg (fun U : Subgroup G => U.map (MulAut.conj a).toMonoidHom) hRS
    dsimp only at hh
    rw [Subgroup.map_inf _ _ (MulAut.conj a).toMonoidHom
      (MulAut.conj a).injective, Subgroup.map_bot, hR, hS] at hh
    exact hh
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G P T
  have hkmap : (P : Subgroup G).map (MulAut.conj k).toMonoidHom = (T : Subgroup G) :=
    congrArg (fun U : Sylow p G => (U : Subgroup G)) hk
  obtain ⟨b, hb, he⟩ := halign k (by rw [hkmap]; exact hPT)
  have hbT : b • Q = T := by
    apply Sylow.ext
    exact he.symm.trans hkmap
  have hbP : b⁻¹ • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr
    ((Subgroup.normalizer (P : Set G)).inv_mem hb)
  refine ⟨b⁻¹*a, ?_, ?_⟩
  · rw [mul_smul, ha, hbP]
  · rw [mul_smul]
    change b⁻¹ • T = Q
    rw [← hbT, inv_smul_smul]

end SymmetricSubgroupAsymptotics.NormalSylowAmbientPairAlignment
