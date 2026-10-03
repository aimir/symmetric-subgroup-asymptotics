import SymmetricSubgroupAsymptotics.AffineNormalComplementGraph
import SymmetricSubgroupAsymptotics.OriginalKernelNormalSubrepresentation

/-!
# Fixed invariant intersections as normal-complement graphs

For one top axis and one invariant intersection, quotient by the literal
intersection.  Every retained original normal subgroup then becomes a normal
complement in the quotient extension.  This file proves the injection and
applies `normalFixedImageComplementFibre_card_le`; in particular the same
intersection is used in the quotient chart and in reconstruction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
variable (pi : G →* B) (hpi : Function.Surjective pi)
variable (A : Rep (ZMod p) B) [Finite A]
variable (E : OriginalKernelModuleChart pi A)

/-- Sectional prime rank passes to every literal quotient. -/
theorem PrimeSectionalRankBound.of_surjective
    {Q : Type} [Group Q]
    {r : ℕ} (h : PrimeSectionalRankBound p G r)
    (q : G →* Q) (hq : Function.Surjective q) :
    PrimeSectionalRankBound p Q r := by
  intro L
  exact PrimeSectionalRankBound.quotient_rank_le p h (L.comap q)
    (q.subgroupComap L) (q.subgroupComap_surjective_of_surjective L hq)

/-- The normal subgroups with one retained top and one retained invariant
intersection inject into the normal-complement fibre after quotienting by
that exact intersection. -/
theorem affineNormalGraphFibre_card_le
    (D : {D : Subgroup B // D.Normal})
    (W : Subrepresentation A.ρ)
    (r H : ℕ)
    (hRank : PrimeSectionalRankBound p G r)
    (hCapacity : ∀ N : {N : Subgroup G // N.Normal},
      representationSchurCapacity
        (E.sectionRepresentation pi A N.1).ρ ≤ H) :
    Nat.card {N : {N : Subgroup G // N.Normal} //
      elementaryLayerTopAxis pi hpi N = D ∧
      E.normalSubrepresentation pi hpi A N.1 = W} ≤ p ^ (H * r) := by
  classical
  let X := {N : {N : Subgroup G // N.Normal} //
    elementaryLayerTopAxis pi hpi N = D ∧
    E.normalSubrepresentation pi hpi A N.1 = W}
  by_cases hX : Nonempty X
  · let N0 : X := Classical.choice hX
    let I : Subgroup G := N0.1.1 ⊓ pi.ker
    letI : I.Normal := inferInstance
    let q : G →* G ⧸ I := QuotientGroup.mk' I
    let beta : (G ⧸ I) →* (G ⧸ (pi.ker ⊔ I)) :=
      OriginalKernelModuleChart.base pi I
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective I
    have hbeta : Function.Surjective beta :=
      OriginalKernelModuleChart.base_surjective pi I
    let D0 : {D : Subgroup (G ⧸ (pi.ker ⊔ I)) // D.Normal} :=
      ⟨(N0.1.1.map q).map beta,
        Subgroup.Normal.map
          (Subgroup.Normal.map N0.1.2 q hq) beta hbeta⟩
    have hinter (N : X) : N.1.1 ⊓ pi.ker = I := by
      have hW : E.normalSubrepresentation pi hpi A N.1.1 =
          E.normalSubrepresentation pi hpi A N0.1.1 :=
        N.2.2.trans N0.2.2.symm
      have hsub :=
        (E.normalSubrepresentation_eq_iff_intersection_eq
          pi hpi A N.1.1 N0.1.1).mp hW
      apply Subgroup.ext
      intro x
      constructor
      · intro hx
        have hxN : (⟨x, hx.2⟩ : pi.ker) ∈
            N.1.1.subgroupOf pi.ker := hx.1
        have hx0 : (⟨x, hx.2⟩ : pi.ker) ∈
            N0.1.1.subgroupOf pi.ker := by
          rw [← hsub]
          exact hxN
        exact ⟨hx0, hx.2⟩
      · intro hx
        have hx0 : (⟨x, hx.2⟩ : pi.ker) ∈
            N0.1.1.subgroupOf pi.ker := hx.1
        have hxN : (⟨x, hx.2⟩ : pi.ker) ∈
            N.1.1.subgroupOf pi.ker := by
          rw [hsub]
          exact hx0
        exact ⟨hxN, hx.2⟩
    have hI_le (N : X) : I ≤ N.1.1 := by
      intro x hx
      have hx' : x ∈ N.1.1 ⊓ pi.ker := by
        rw [hinter N]
        exact hx
      exact hx'.1
    have hsup (N : X) : pi.ker ⊔ N.1.1 = pi.ker ⊔ N0.1.1 := by
      have haxis : elementaryLayerTopAxis pi hpi N.1 =
          elementaryLayerTopAxis pi hpi N0.1 :=
        N.2.1.trans N0.2.1.symm
      have hmap := congrArg (fun Z : {D : Subgroup B // D.Normal} => Z.1) haxis
      change (pi.ker ⊔ N.1.1).map pi =
        (pi.ker ⊔ N0.1.1).map pi at hmap
      simpa only [Subgroup.comap_map_eq_self le_sup_left] using
        congrArg (Subgroup.comap pi) hmap
    have hcomp : beta.comp q = QuotientGroup.mk' (pi.ker ⊔ I) := by
      ext x
      rfl
    have hkernel_map_bot : pi.ker.map (beta.comp q) = ⊥ := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        apply Subgroup.mem_bot.mpr
        rw [hcomp]
        exact (QuotientGroup.eq_one_iff (N := pi.ker ⊔ I) x).mpr
          (Subgroup.mem_sup_left hx)
      · exact bot_le
    have himage (N : X) : (N.1.1.map q).map beta = D0.1 := by
      change (N.1.1.map q).map beta = (N0.1.1.map q).map beta
      rw [Subgroup.map_map, Subgroup.map_map]
      calc
        N.1.1.map (beta.comp q) =
            (pi.ker ⊔ N.1.1).map (beta.comp q) := by
          rw [Subgroup.map_sup, hkernel_map_bot, bot_sup_eq]
        _ = (pi.ker ⊔ N0.1.1).map (beta.comp q) := by rw [hsup N]
        _ = N0.1.1.map (beta.comp q) := by
          rw [Subgroup.map_sup, hkernel_map_bot, bot_sup_eq]
    have hinf (N : X) :
        N.1.1.map q ⊓ beta.ker = ⊥ := by
      apply Subgroup.comap_injective hq
      rw [Subgroup.comap_inf, QuotientGroup.comap_map_mk',
        MonoidHom.comap_bot, QuotientGroup.ker_mk']
      have hbetaKer : beta.ker.comap q = pi.ker ⊔ I := by
        change (beta.comp q).ker = pi.ker ⊔ I
        rw [hcomp, QuotientGroup.ker_mk']
      rw [hbetaKer, sup_eq_right.mpr (hI_le N),
        sup_eq_left.mpr inf_le_right, hinter N]
    let f : X → NormalFixedImageComplementFibre beta D0 := fun N =>
      ⟨⟨N.1.1.map q, Subgroup.Normal.map N.1.2 q hq⟩,
        himage N, hinf N⟩
    have hf : Function.Injective f := by
      intro N M hNM
      apply Subtype.ext
      apply Subtype.ext
      have hmap : N.1.1.map q = M.1.1.map q :=
        congrArg (fun Z : NormalFixedImageComplementFibre beta D0 => Z.1.1) hNM
      have hcomap := congrArg (Subgroup.comap q) hmap
      rw [QuotientGroup.comap_map_mk', QuotientGroup.comap_map_mk',
        sup_eq_right.mpr (hI_le N), sup_eq_right.mpr (hI_le M)] at hcomap
      exact hcomap
    have hRankQ : PrimeSectionalRankBound p (G ⧸ I) r :=
      hRank.of_surjective p q hq
    have hcap : representationSchurCapacity
        (E.sectionRepresentation pi A I).ρ ≤ H :=
      hCapacity ⟨I, inferInstance⟩
    letI : Finite (E.sectionRepresentation pi A I) :=
      Finite.of_surjective (E.normalSpace pi A I).mkQ
        (E.normalSpace pi A I).mkQ_surjective
    exact (Nat.card_le_card_of_injective f hf).trans
      (normalFixedImageComplementFibre_card_le p beta hbeta
        (E.sectionRepresentation pi A I)
        (by simpa only [beta] using E.quotientChart pi A I) D0 r H hRankQ hcap)
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    simp

end SymmetricSubgroupAsymptotics

end
