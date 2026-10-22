import SymmetricSubgroupAsymptotics.CFSGTwistedA2OppositeUnipotent

/-! Literal natural two-root join and its comparison with the SAME
original fixed-source join. Every natural word has an actual original
word image; no whole-unitary recognition is supplied as a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2OriginalRelations
open CFSGTwistedA2HighestRootUnits CFSGSerreOrdinaryTwists CFSGSerreFixedRootElements

def naturalRootGenerated (q : CFSG.PrimePower) (t : q.Extension 2) :
    Subgroup (NaturalElementary (q.Extension 2) 2) :=
  naturalUnipotent q ⊔ (naturalUnipotent q).map
    (MulAut.conj (weylNatural (q.Extension 2) t)).toMonoidHom

theorem weylNatural_mem_rootGenerated (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht0 : t ≠ 0) (ht : t ^ q.order = -t) :
    weylNatural (q.Extension 2) t ∈ naturalRootGenerated q t := by
  have hu : highest (q.Extension 2) t ∈ naturalUnipotent q :=
    ⟨0, t, highest_norm q t ht, highest_eq_upperNatural _ _ t⟩
  have ho : opposite (q.Extension 2) (-t⁻¹) ∈ (naturalUnipotent q).map
      (MulAut.conj (weylNatural (q.Extension 2) t)).toMonoidHom :=
    ⟨highest (q.Extension 2) t, hu, weyl_conjugate_highest _ t ht0⟩
  have hlu : naturalUnipotent q ≤ naturalRootGenerated q t := le_sup_left
  have hlo : (naturalUnipotent q).map
      (MulAut.conj (weylNatural (q.Extension 2) t)).toMonoidHom ≤
        naturalRootGenerated q t := le_sup_right
  exact (naturalRootGenerated q t).mul_mem
    ((naturalRootGenerated q t).mul_mem (hlu hu) (hlo ho)) (hlu hu)

theorem naturalRootGenerated_fixed (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) (u : NaturalElementary (q.Extension 2) 2)
    (hu : u ∈ naturalRootGenerated q t) :
    diagramFieldUnitHom (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom u.val = u.val := by
  let f := diagramFieldUnitHom (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
  let F := (f.eqLocus (MonoidHom.id ((Mat (q.Extension 2) 2)ˣ))).comap
    (NaturalElementary (q.Extension 2) 2).subtype
  have hU : naturalUnipotent q ≤ F := by
    intro v hv
    exact naturalUnipotent_fixed q ⟨v, hv⟩
  have hO : (naturalUnipotent q).map
      (MulAut.conj (weylNatural (q.Extension 2) t)).toMonoidHom ≤ F := by
    rintro _ ⟨v, hv, rfl⟩
    change diagramFieldUnitHom (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
      ((weylNatural (q.Extension 2) t).val * v.val *
        ((weylNatural (q.Extension 2) t).val)⁻¹) = _
    rw [map_mul, map_mul, map_inv, weylNatural_fixed q t ht,
      naturalUnipotent_fixed q ⟨v, hv⟩]
    rfl
  exact (sup_le hU hO) hu

theorem naturalRootGenerated_map_le_original (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) :
    (naturalRootGenerated q t).map (elementaryToModel (q.Extension 2)) ≤
      (rootGenerated q t ht).map
        (fixedToModel A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)) := by
  change (naturalUnipotent q ⊔ (naturalUnipotent q).map
      (MulAut.conj (weylNatural (q.Extension 2) t)).toMonoidHom).map _ ≤ _
  rw [Subgroup.map_sup]
  apply sup_le
  · rintro _ ⟨u, hu, rfl⟩
    let v : naturalUnipotent q := ⟨u, hu⟩
    have hv : unipotentToOriginalFixed q v ∈ rootGenerated q t ht :=
      (show originalUnipotent q ≤ rootGenerated q t ht from le_sup_left) ⟨v, rfl⟩
    exact ⟨unipotentToOriginalFixed q v, hv, rfl⟩
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    let v : naturalUnipotent q := ⟨u, hu⟩
    let g := originalWeyl q t ht * unipotentToOriginalFixed q v * (originalWeyl q t ht)⁻¹
    have hg : g ∈ rootGenerated q t ht :=
      (show oppositeOriginalUnipotent q t ht ≤ rootGenerated q t ht from le_sup_right)
        ⟨unipotentToOriginalFixed q v, ⟨v, rfl⟩, rfl⟩
    refine ⟨g, hg, ?_⟩
    change fixedToModel A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)
        (originalWeyl q t ht * unipotentToOriginalFixed q v * (originalWeyl q t ht)⁻¹) =
      elementaryToModel (q.Extension 2)
        (weylNatural (q.Extension 2) t * u * (weylNatural (q.Extension 2) t)⁻¹)
    simp only [map_mul, map_inv]
    rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
