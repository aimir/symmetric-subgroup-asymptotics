import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.FinCases

import Mathlib.GroupTheory.Frattini

/-! The SAME actual shear-coordinate argument with a genuinely Frattini
kernel needs no extra kernel generators. This is a nongenerating-kernel
statement, not a claim that arbitrary normal generators pay ordinary
rank. The original coordinate map and conjugating element remain fixed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FrattiniShearCoordinateOrdinaryGenerators

variable {G R K : Type} [Group G] [Finite G] [Group R] [Finite R] [Field K]
    (p : ℕ) [Fact p.Prime] [Module (ZMod p) K]

theorem exists_generating_finset (m : ℕ) (b : Module.Basis (Fin m) (ZMod p) K)
    (iota : R →* G) (phi : R →* Multiplicative (Fin 2 → K))
    (hphi : Function.Surjective phi) (a : G) (c : R → R)
    (hc : ∀ z : R, iota (c z) = a*iota z*a⁻¹)
    (hshear : ∀ z : R, (phi (c z)).toAdd =
      (phi z).toAdd+Pi.single 0 ((phi z).toAdd 1))
    (hgen : iota.range ⊔ Subgroup.zpowers a = ⊤)
    (hkernel : ∀ z : R, z ∈ phi.ker → iota z ∈ frattini G) :
    ∃ T : Finset G, Subgroup.closure (T : Set G) = ⊤ ∧
      T.card ≤ m+1 := by
  classical
  choose z hz using (fun j : Fin m => hphi (Multiplicative.ofAdd (Pi.single 1 (b j))))
  let B := Finset.univ.image (fun j : Fin m => iota (z j))
  let T := insert a B
  let H0 := Subgroup.closure (T : Set G)
  let H := H0 ⊔ frattini G
  have ha : a ∈ H := (show H0 ≤ H from le_sup_left)
    (Subgroup.subset_closure (Finset.mem_insert_self _ _))
  have hzH : ∀ j : Fin m, iota (z j) ∈ H := by
    intro j
    apply (show H0 ≤ H from le_sup_left)
    apply Subgroup.subset_closure
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
  let L := H.comap iota
  have hker : phi.ker ≤ L := by
    intro z hz
    exact (show frattini G ≤ H from le_sup_right) (hkernel z hz)
  let W : Submodule (ZMod p) (Fin 2 → K) :=
    AddSubgroup.toZModSubmodule p (L.map phi).toAddSubgroup'
  have hsecond : ∀ j : Fin m, Pi.single 1 (b j) ∈ W := by
    intro j
    change Multiplicative.ofAdd (Pi.single 1 (b j)) ∈ L.map phi
    exact ⟨z j,hzH j,hz j⟩
  have hfirst : ∀ j : Fin m, Pi.single 0 (b j) ∈ W := by
    intro j
    have hconj : c (z j) ∈ L := by
      change iota (c (z j)) ∈ H
      rw [hc]
      exact H.mul_mem (H.mul_mem ha (hzH j)) (H.inv_mem ha)
    have hv : (phi (c (z j))).toAdd ∈ W := by
      change Multiplicative.ofAdd (phi (c (z j))).toAdd ∈ L.map phi
      exact ⟨c (z j),hconj,rfl⟩
    have heq : (phi (c (z j))).toAdd-Pi.single 1 (b j) = Pi.single 0 (b j) := by
      rw [hshear,hz j]
      simp only [toAdd_ofAdd,Pi.single_eq_same]
      abel
    rw [←heq]
    exact W.sub_mem hv (hsecond j)
  have haxis (j : Fin 2) (hj : ∀ i : Fin m, Pi.single j (b i) ∈ W) (x : K) :
      Pi.single j x ∈ W := by
    let f : K →ₗ[ZMod p] (Fin 2 → K) := LinearMap.single (ZMod p) (fun _ : Fin 2 => K) j
    have hle : Submodule.span (ZMod p) (Set.range b) ≤ W.comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hj i
    have hx : x ∈ Submodule.span (ZMod p) (Set.range b) := by rw [b.span_eq]; trivial
    exact hle hx
  have hW : W = ⊤ := by
    apply top_unique
    intro v _
    have hv := W.add_mem (haxis 0 hfirst (v 0)) (haxis 1 hsecond (v 1))
    have heq : Pi.single 0 (v 0)+Pi.single 1 (v 1) = v := by
      ext j
      fin_cases j <;> simp
    rwa [heq] at hv
  have hmap : L.map phi = ⊤ := by
    apply top_unique
    intro v _
    have hv : v.toAdd ∈ W := by rw [hW]; trivial
    exact hv
  have hL : L = ⊤ := by
    have hh := congrArg (Subgroup.comap phi) hmap
    rw [Subgroup.comap_map_eq,Subgroup.comap_top,sup_eq_left.mpr hker] at hh
    exact hh
  have hR : iota.range ≤ H := by
    rintro _ ⟨x,rfl⟩
    have hx : x ∈ L := by rw [hL]; trivial
    exact hx
  have hH : H = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le hR (Subgroup.zpowers_le.mpr ha)
  have hH0 : H0 = ⊤ := frattini_nongenerating hH
  refine ⟨T,hH0,?_⟩
  have hB : B.card ≤ m := (Finset.card_image_le).trans_eq (by simp)
  have hT : T.card ≤ B.card+1 := Finset.card_insert_le _ _
  omega

theorem genRank_le (m : ℕ) (b : Module.Basis (Fin m) (ZMod p) K)
    (iota : R →* G) (phi : R →* Multiplicative (Fin 2 → K))
    (hphi : Function.Surjective phi) (a : G) (c : R → R)
    (hc : ∀ z : R, iota (c z) = a*iota z*a⁻¹)
    (hshear : ∀ z : R, (phi (c z)).toAdd =
      (phi z).toAdd+Pi.single 0 ((phi z).toAdd 1))
    (hgen : iota.range ⊔ Subgroup.zpowers a = ⊤)
    (hkernel : ∀ z : R, z ∈ phi.ker → iota z ∈ frattini G) :
    MarkedC4.genRank G ≤ m+1 := by
  obtain ⟨T,hT,hcard⟩ := exists_generating_finset p m b iota phi hphi a c hc hshear hgen hkernel
  exact (MarkedC4.genRank_le hT).trans hcard

end SymmetricSubgroupAsymptotics.FrattiniShearCoordinateOrdinaryGenerators
