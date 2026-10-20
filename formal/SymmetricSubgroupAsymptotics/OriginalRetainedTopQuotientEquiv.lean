import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Two actual normal denominators may be taken in either order. The
canonical top denominator is the image of the ORIGINAL N, never an
independently selected isomorphic subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalRetainedTopQuotientEquiv

variable {G C : Type} [Group G] [Group C]

instance mappedNormal (e : G ≃* C) (N : Subgroup G) [hN : N.Normal] :
    (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective

noncomputable def quotientSwap (E N : Subgroup G) [E.Normal] [N.Normal] :
    (G ⧸ N) ⧸ E.map (QuotientGroup.mk' N) ≃*
      (G ⧸ E) ⧸ N.map (QuotientGroup.mk' E) := by
  have hN : (E ⊔ N).map (QuotientGroup.mk' N) = E.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq]
  have hE : (E ⊔ N).map (QuotientGroup.mk' E) = N.map (QuotientGroup.mk' E) := by
    rw [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq]
  let eN : (G ⧸ N) ⧸ E.map (QuotientGroup.mk' N) ≃* G ⧸ (E ⊔ N) :=
    (QuotientGroup.quotientMulEquivOfEq hN.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient N (E ⊔ N) le_sup_right)
  let eE : (G ⧸ E) ⧸ N.map (QuotientGroup.mk' E) ≃* G ⧸ (E ⊔ N) :=
    (QuotientGroup.quotientMulEquivOfEq hE.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient E (E ⊔ N) le_sup_left)
  exact eN.trans eE.symm

noncomputable def quotientEquivMap (e : G ≃* C) (N : Subgroup G) [N.Normal] :
    G ⧸ N ≃* C ⧸ N.map e.toMonoidHom := by
  let f : G ⧸ N →* C ⧸ N.map e.toMonoidHom :=
    QuotientGroup.map N (N.map e.toMonoidHom) e.toMonoidHom
      (Subgroup.le_comap_map e.toMonoidHom N)
  have hback : N.map e.toMonoidHom ≤ N.comap e.symm.toMonoidHom := by
    rintro _ ⟨x,hx,rfl⟩
    change e.symm (e x) ∈ N
    simpa only [e.symm_apply_apply] using hx
  let g : C ⧸ N.map e.toMonoidHom →* G ⧸ N :=
    QuotientGroup.map (N.map e.toMonoidHom) N e.symm.toMonoidHom hback
  exact {
    toFun := f
    invFun := g
    left_inv := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H x =>
        change QuotientGroup.mk' N (e.symm (e x)) = QuotientGroup.mk' N x
        rw [e.symm_apply_apply]
    right_inv := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H x =>
        change QuotientGroup.mk' (N.map e.toMonoidHom) (e (e.symm x)) =
          QuotientGroup.mk' (N.map e.toMonoidHom) x
        rw [e.apply_symm_apply]
    map_mul' := f.map_mul }

/-- The unchanged retained top quotient with its literal original normal
image transported through the supplied actual canonical chart. -/
noncomputable def retainedTopEquiv (E N : Subgroup G) [E.Normal] [N.Normal]
    (e : G ⧸ E ≃* C) :
    (G ⧸ N) ⧸ E.map (QuotientGroup.mk' N) ≃*
      C ⧸ (N.map (QuotientGroup.mk' E)).map e.toMonoidHom :=
  (quotientSwap E N).trans (quotientEquivMap e (N.map (QuotientGroup.mk' E)))

end SymmetricSubgroupAsymptotics.OriginalRetainedTopQuotientEquiv
end
