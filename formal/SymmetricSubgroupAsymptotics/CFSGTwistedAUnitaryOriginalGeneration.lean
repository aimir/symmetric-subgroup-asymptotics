import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryWholeUpperDerived
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPullbackTransport

/-! The literal original fixed-source derived group is the join of its
actual U and its conjugate by the SAME original signed reversal. The
reverse inclusion uses the proved actual isometric lift of every
original commutator element and the Gaussian theorem on that lift. No
ambient simplicity, fixed-lift surjectivity, full-SU equality or source
kernel hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAIntervalSource CFSGSerreOrdinaryTwists CFSGSerreFixedRootElements

def originalOppositeUnipotent (q : CFSG.PrimePower) (r : ℕ) : Subgroup (Fixed r q) :=
  (originalUnipotent r q).map (MulAut.conj (originalReversal q r)).toMonoidHom

def originalUpperOppositeJoin (q : CFSG.PrimePower) (r : ℕ) : Subgroup (Fixed r q) :=
  originalUnipotent r q ⊔ originalOppositeUnipotent q r

def originalToModel (q : CFSG.PrimePower) (r : ℕ) :
    Fixed r q →* CFSG.Models.Chevalley.Model (CartanMatrix.A r) (q.Extension 2) :=
  fixedToModel (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)

theorem naturalJoin_map_le_original (q : CFSG.PrimePower) (r : ℕ) :
    (naturalUpperOppositeJoin q r).map (elementaryToModel (q.Extension 2) r) ≤
      (originalUpperOppositeJoin q r).map (originalToModel q r) := by
  change (naturalUnipotent r q ⊔ (naturalUnipotent r q).map
    (MulAut.conj (reversalNatural q r)).toMonoidHom).map _ ≤ _
  rw [Subgroup.map_sup]
  apply sup_le
  · rintro _ ⟨u, hu, rfl⟩
    let v : naturalUnipotent r q := ⟨u, hu⟩
    have hv : unipotentToOriginalFixed r q v ∈ originalUpperOppositeJoin q r :=
      (show originalUnipotent r q ≤ originalUpperOppositeJoin q r from le_sup_left) ⟨v, rfl⟩
    exact ⟨unipotentToOriginalFixed r q v, hv, rfl⟩
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    let v : naturalUnipotent r q := ⟨u, hu⟩
    let g := originalReversal q r * unipotentToOriginalFixed r q v * (originalReversal q r)⁻¹
    have hg : g ∈ originalUpperOppositeJoin q r :=
      (show originalOppositeUnipotent q r ≤ originalUpperOppositeJoin q r from le_sup_right)
        ⟨unipotentToOriginalFixed r q v, ⟨v, rfl⟩, rfl⟩
    refine ⟨g, hg, ?_⟩
    change originalToModel q r
      (originalReversal q r * unipotentToOriginalFixed r q v * (originalReversal q r)⁻¹) =
      elementaryToModel (q.Extension 2) r
        (reversalNatural q r * u * (reversalNatural q r)⁻¹)
    simp only [map_mul, map_inv]
    rfl

theorem naturalFixed_image_mem_original_join (q : CFSG.PrimePower) (r : ℕ)
    (u : naturalFixed r q) :
    naturalFixedToOriginal q r u ∈ originalUpperOppositeJoin q r := by
  have hm := naturalJoin_map_le_original q r
    ⟨u.val, naturalFixed_mem_join q r u, rfl⟩
  obtain ⟨x, hx, he⟩ := hm
  have hxu : x = naturalFixedToOriginal q r u := by
    apply Subtype.ext
    exact congrArg (fun z : CFSG.Models.Chevalley.Model (CartanMatrix.A r) (q.Extension 2) => z.val) he
  rwa [hxu] at hx

theorem originalReversal_mem_join (q : CFSG.PrimePower) (r : ℕ) :
    originalReversal q r ∈ originalUpperOppositeJoin q r :=
  naturalFixed_image_mem_original_join q r (reversalFixed q r)

theorem original_derived_le_join (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    commutator (Fixed r q) ≤ originalUpperOppositeJoin q r := by
  intro g hg
  obtain ⟨u, hact, _, hform⟩ := original_derived_isometric_lift r hr q ⟨g, hg⟩
  have hu : u ∈ naturalFixed r q :=
    unit_fixed_of_isometric (q.Extension 2) r (definingFieldAutomorphism q 2).toRingHom
      u.val hform
  let U : naturalFixed r q := ⟨u, hu⟩
  have he : naturalFixedToOriginal q r U = g := by
    apply twistedFixedAction_injective q r
    change CFSGTwistedANaturalMatrices.naturalAction (q.Extension 2) r
      (elementaryToModel (q.Extension 2) r u) = twistedDerivedAction r q ⟨g, hg⟩
    rw [elementaryToModel_action]
    exact hact
  rw [← he]
  exact naturalFixed_image_mem_original_join q r U

theorem original_join_le_derived (q : CFSG.PrimePower) (s : ℕ) :
    originalUpperOppositeJoin q (s + 3) ≤ commutator (Fixed (s + 3) q) := by
  apply sup_le (originalUnipotent_le_derived q s)
  rintro g ⟨u, hu, rfl⟩
  exact (inferInstance : (commutator (Fixed (s + 3) q)).Normal).conj_mem
    u (originalUnipotent_le_derived q s hu) (originalReversal q (s + 3))

theorem originalUpperOppositeJoin_eq_derived (q : CFSG.PrimePower) (s : ℕ) :
    originalUpperOppositeJoin q (s + 3) = commutator (Fixed (s + 3) q) :=
  le_antisymm (original_join_le_derived q s) (original_derived_le_join q (s + 3) (by omega))

theorem originalReversal_mem_derived (q : CFSG.PrimePower) (s : ℕ) :
    originalReversal q (s + 3) ∈ commutator (Fixed (s + 3) q) :=
  original_join_le_derived q s (originalReversal_mem_join q (s + 3))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
