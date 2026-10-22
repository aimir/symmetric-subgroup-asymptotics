import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitriangularSimilitude
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentNormalizerSoluble
import SymmetricSubgroupAsymptotics.CFSGUpperTriangularPSubgroups
import Mathlib.GroupTheory.Sylow

/-! Every defining-characteristic p-subgroup of the ORIGINAL normalizer
lies in the original q^3 unipotent subgroup. A Sylow upstairs maps onto
the target p-group; no coprime central-kernel splitting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists

theorem pGroup_upper_diagonal_one {K G : Type} [Field K] [Group G]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hG : IsPGroup p G)
    (rho : G →* Mat K 2) (hupper : ∀ g, (rho g).BlockTriangular id)
    (g : G) (i : Fin 3) : rho g i i = 1 := by
  obtain ⟨k, hk⟩ := hG g
  have hp : rho g ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have he := congrArg (fun M : Mat K 2 => M i i) hp
  dsimp only at he
  rw [CFSGUpperUnitriangular.upper_diag_pow (hupper g), Matrix.one_apply_eq] at he
  apply iterateFrobenius_inj K p k
  simpa only [iterateFrobenius_def, one_pow] using he

theorem pullbackSource_mem_unipotent_of_unitriangular (q : CFSG.PrimePower)
    (p : fixedNaturalPullback 2 q)
    (hu : (pullbackMatrix 2 q p : Mat (q.Extension 2) 2).BlockTriangular id)
    (hd : ∀ i, (pullbackMatrix 2 q p : Mat (q.Extension 2) 2) i i = 1) :
    pullbackSource 2 q p ∈ originalUnipotent q := by
  obtain ⟨c, _, hc⟩ := pullbackMatrix_similitude 2 (by decide) q p
  obtain ⟨a, b, hab, hm⟩ := upperArray_of_unitriangular_similitude (q.Extension 2)
    (definingFieldAutomorphism q 2) (fun x => extension_two_pow_twice q x)
    (pullbackMatrix 2 q p : Mat (q.Extension 2) 2) c hu hd hc
  let v : naturalUnipotent q :=
    ⟨upperNatural (q.Extension 2) (definingFieldAutomorphism q 2) a b, a, b, hab, rfl⟩
  have helem : pullbackElementary 2 q p = v.val := by
    apply Subtype.ext
    apply Units.ext
    exact hm.trans (upperNatural_val _ _ a b).symm
  refine ⟨v, ?_⟩
  apply twistedFixedAction_two_injective q
  rw [unipotentToOriginalFixed_action, ← pullback_action_eq, helem]

theorem original_normalizer_pSubgroups (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (P : Subgroup (OriginalFixedA 2 q)) (hP : IsPGroup q.prime P)
    (hPN : P ≤ Subgroup.normalizer (originalUnipotent q : Set (OriginalFixedA 2 q))) :
    P ≤ originalUnipotent q := by
  letI : Finite (fixedNaturalPullback 2 q) :=
    Finite.of_injective (pullbackMatrix 2 q) (pullbackMatrix_two_injective q)
  let R := P.comap (pullbackSource 2 q)
  let f : R →* P :=
    { toFun := fun u => ⟨pullbackSource 2 q u.val, u.property⟩
      map_one' := by apply Subtype.ext; exact map_one (pullbackSource 2 q)
      map_mul' := fun u v => by apply Subtype.ext; exact map_mul (pullbackSource 2 q) u.val v.val }
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨u, hu⟩ := pullbackSource_surjective 2 (by decide) q g.val
    refine ⟨⟨u, ?_⟩, ?_⟩
    · change pullbackSource 2 q u ∈ P
      rw [hu]
      exact g.property
    · exact Subtype.ext hu
  let S : Sylow q.prime R := default
  have htop : ((S.mapSurjective hf : Sylow q.prime P) : Subgroup P) = ⊤ :=
    ((S.mapSurjective hf).3 (hP.to_subgroup ⊤) le_top).symm
  intro g hg
  have hgmap : (⟨g, hg⟩ : P) ∈ (S : Subgroup R).map f := by
    rw [← Sylow.coe_mapSurjective hf S, htop]
    exact Subgroup.mem_top _
  obtain ⟨u, hu, he⟩ := hgmap
  let rho : S →* Mat (q.Extension 2) 2 :=
    (Units.coeHom (Mat (q.Extension 2) 2)).comp
      ((pullbackMatrix 2 q).comp (R.subtype.comp (S : Subgroup R).subtype))
  have hupper (x : S) : (rho x).BlockTriangular id :=
    pullback_normalizer_upper q hq x.val.val (hPN x.val.property)
  have hd : ∀ i, (pullbackMatrix 2 q u.val : Mat (q.Extension 2) 2) i i = 1 := by
    intro i
    exact pGroup_upper_diagonal_one q.prime S.isPGroup' rho hupper ⟨u, hu⟩ i
  have hm := pullbackSource_mem_unipotent_of_unitriangular q u.val
    (hupper ⟨u, hu⟩) hd
  have he' : pullbackSource 2 q u.val = g := congrArg (fun x : P => x.val) he
  rw [he'] at hm
  exact hm

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
