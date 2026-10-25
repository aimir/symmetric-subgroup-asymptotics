import SymmetricSubgroupAsymptotics.FrattiniShearCoordinateOrdinaryGenerators

/-! An actual middle subgroup and one literal three-coordinate shear
save a whole prime-field axis in ordinary radical generation. The
parameter kernel is Frattini in the SAME ambient group; all middle
generators and the actual range factorization are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FrattiniThreeCoordinateShearOrdinaryGenerators

variable {G R M K : Type} [Group G] [Finite G] [Group R] [Finite R]
    [Group M] [Field K] (p : ℕ) [Fact p.Prime] [Module (ZMod p) K]

theorem exists_generating_finset (m : ℕ) (b : Module.Basis (Fin m) (ZMod p) K)
    (iota : R →* G) (phi : R →* Multiplicative (Fin 3 → K))
    (hphi : Function.Surjective phi) (psi : M →* G) (S : Finset M)
    (hS : Subgroup.closure (S : Set M) = ⊤) (a : M) (c : R → R)
    (hc : ∀ z : R, iota (c z) = psi a*iota z*(psi a)⁻¹)
    (hshear : ∀ z : R, (phi (c z)).toAdd =
      (phi z).toAdd+Pi.single 0 ((phi z).toAdd 2))
    (hgen : iota.range ⊔ psi.range = ⊤)
    (hkernel : ∀ z : R, z ∈ phi.ker → iota z ∈ frattini G) :
    ∃ T : Finset G, Subgroup.closure (T : Set G) = ⊤ ∧
      T.card ≤ 2*m+S.card := by
  classical
  choose z hz using (fun axis : Fin 2 => fun j : Fin m =>
    hphi (Multiplicative.ofAdd (Pi.single axis.succ (b j))))
  let B := Finset.univ.image (fun x : Fin 2 × Fin m => iota (z x.1 x.2))
  let T := B ∪ S.image psi
  let H0 := Subgroup.closure (T : Set G)
  let H := H0 ⊔ frattini G
  have hM : psi.range ≤ H := by
    let F := H.comap psi
    have hle : Subgroup.closure (S : Set M) ≤ F := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      apply (show H0 ≤ H from le_sup_left)
      apply Subgroup.subset_closure
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    rw [hS] at hle
    rintro _ ⟨x,rfl⟩
    exact hle (Subgroup.mem_top x)
  have ha : psi a ∈ H := hM ⟨a,rfl⟩
  have hzH : ∀ axis : Fin 2, ∀ j : Fin m, iota (z axis j) ∈ H := by
    intro axis j
    apply (show H0 ≤ H from le_sup_left)
    apply Subgroup.subset_closure
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(axis,j),Finset.mem_univ _,rfl⟩)
  let L := H.comap iota
  have hker : phi.ker ≤ L := by
    intro z hz
    exact (show frattini G ≤ H from le_sup_right) (hkernel z hz)
  let W : Submodule (ZMod p) (Fin 3 → K) :=
    AddSubgroup.toZModSubmodule p (L.map phi).toAddSubgroup'
  have hseed : ∀ axis : Fin 2, ∀ j : Fin m, Pi.single axis.succ (b j) ∈ W := by
    intro axis j
    change Multiplicative.ofAdd (Pi.single axis.succ (b j)) ∈ L.map phi
    exact ⟨z axis j,hzH axis j,hz axis j⟩
  have hfirst : ∀ j : Fin m, Pi.single 0 (b j) ∈ W := by
    intro j
    have hconj : c (z 1 j) ∈ L := by
      change iota (c (z 1 j)) ∈ H
      rw [hc]
      exact H.mul_mem (H.mul_mem ha (hzH 1 j)) (H.inv_mem ha)
    have hv : (phi (c (z 1 j))).toAdd ∈ W := by
      change Multiplicative.ofAdd (phi (c (z 1 j))).toAdd ∈ L.map phi
      exact ⟨c (z 1 j),hconj,rfl⟩
    have heq : (phi (c (z 1 j))).toAdd-Pi.single 2 (b j) = Pi.single 0 (b j) := by
      rw [hshear,hz 1 j]
      change (Pi.single (2 : Fin 3) (b j) : Fin 3 → K)+
        (Pi.single (0 : Fin 3) ((Pi.single (2 : Fin 3) (b j) : Fin 3 → K) (2 : Fin 3)) : Fin 3 → K)-
        (Pi.single (2 : Fin 3) (b j) : Fin 3 → K) =
        (Pi.single (0 : Fin 3) (b j) : Fin 3 → K)
      rw [Pi.single_eq_same]
      abel
    rw [←heq]
    exact W.sub_mem hv (hseed 1 j)
  have haxis (j : Fin 3) (hj : ∀ i : Fin m, Pi.single j (b i) ∈ W) (x : K) :
      Pi.single j x ∈ W := by
    let f : K →ₗ[ZMod p] (Fin 3 → K) := LinearMap.single (ZMod p) (fun _ : Fin 3 => K) j
    have hle : Submodule.span (ZMod p) (Set.range b) ≤ W.comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hj i
    have hx : x ∈ Submodule.span (ZMod p) (Set.range b) := by rw [b.span_eq]; trivial
    exact hle hx
  have hW : W = ⊤ := by
    apply top_unique
    intro v _
    have hv := W.add_mem (W.add_mem (haxis 0 hfirst (v 0))
      (haxis 1 (hseed 0) (v 1))) (haxis 2 (hseed 1) (v 2))
    have heq : Pi.single 0 (v 0)+Pi.single 1 (v 1)+Pi.single 2 (v 2) = v := by
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
    exact sup_le hR hM
  have hH0 : H0 = ⊤ := frattini_nongenerating hH
  refine ⟨T,hH0,?_⟩
  have hB : B.card ≤ 2*m := Finset.card_image_le.trans_eq (by simp)
  have hSimage : (S.image psi).card ≤ S.card := Finset.card_image_le
  have hT : T.card ≤ B.card+(S.image psi).card := Finset.card_union_le B (S.image psi)
  omega

theorem genRank_le (m : ℕ) (b : Module.Basis (Fin m) (ZMod p) K)
    (iota : R →* G) (phi : R →* Multiplicative (Fin 3 → K))
    (hphi : Function.Surjective phi) (psi : M →* G) (S : Finset M)
    (hS : Subgroup.closure (S : Set M) = ⊤) (a : M) (c : R → R)
    (hc : ∀ z : R, iota (c z) = psi a*iota z*(psi a)⁻¹)
    (hshear : ∀ z : R, (phi (c z)).toAdd =
      (phi z).toAdd+Pi.single 0 ((phi z).toAdd 2))
    (hgen : iota.range ⊔ psi.range = ⊤)
    (hkernel : ∀ z : R, z ∈ phi.ker → iota z ∈ frattini G) :
    MarkedC4.genRank G ≤ 2*m+S.card := by
  obtain ⟨T,hT,hcard⟩ := exists_generating_finset p m b iota phi hphi psi S hS a c hc hshear hgen hkernel
  exact (MarkedC4.genRank_le hT).trans hcard

end SymmetricSubgroupAsymptotics.FrattiniThreeCoordinateShearOrdinaryGenerators
