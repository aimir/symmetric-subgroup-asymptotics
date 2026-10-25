import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiBorelHom
import SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! The genuine middle Suzuki Borel acts on the SAME original Ree F4
cosets. A surviving actual central parameter moves a point, and the
quadratic/torus argument uses its one pulled-back stabilizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiIndex
open CFSGReeFFourFieldParameters CFSGReeFFourMiddleSuzukiBorelHom
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourPerfectProjection CFSGSuzukiCentralExtensionLayers
open CFSGSuzukiCentralAnnihilatorIndex CFSGSuzukiQuadraticTorusStabilizerIndex

theorem middle_suzuki_le_proper_index (m : ℕ) (hm : 0 < m)
    [IsSimpleGroup (CFSG.Models.ReeF4 m)]
    (H : Subgroup (CFSG.Models.ReeF4 m)) (hH : H≠⊤) :
    (2^(2*m+1)-1)*2^(m+1)≤H.index := by
  letI : Finite (originalModelFixed m) :=
    Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)
  letI : Finite (CFSG.Models.ReeF4 m) :=
    Finite.of_surjective (fixedToOriginal m hm) (fixedToOriginal_surjective m hm)
  let c : Multiplicative (Field m) := Multiplicative.ofAdd 1
  let f : Multiplicative (Field m) →* CFSG.Models.ReeF4 m :=
    (extensionHom m hm).comp (SemidirectProduct.inl.comp (centralHom m))
  have hc : f c≠1 := by
    intro he
    have hz : c=1 := extensionHom_central_injective m hm
      (he.trans (map_one f).symm)
    exact one_ne_zero (congrArg (fun z : Multiplicative (Field m) => z.toAdd) hz)
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH (f c) hc
  letI : MulAction (Borel m) (CFSG.Models.ReeF4 m ⧸ H) :=
    MulAction.compHom _ (extensionHom m hm)
  let M : Subgroup (Borel m) := MulAction.stabilizer (Borel m) x
  have hM : ¬(centralHom m).range ≤ M.comap SemidirectProduct.inl := by
    intro h
    exact hx (h ⟨c,rfl⟩)
  have hb : (Nat.card (Field m)-1)*2^(m+1)≤Nat.card (CFSG.Models.ReeF4 m ⧸ H) := by
    calc
      _ ≤ M.index := quadratic_torus_le_index m M hM
      _ = (MulAction.orbit (Borel m) x).ncard := MulAction.index_stabilizer _ _
      _ ≤ _ := Set.ncard_le_card _
  rw [field_card] at hb
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiIndex
