import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerPilot

/-! Shared exact-image quotient theorem for signed paired-Singer clients.
The coordinate projectors and local orbits are witnessed by actual words
in the displayed original linear generators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryThreeQuartetPairedOrbitSocles
open BinaryPlaneWreathIrreducible

variable {R : Type} [Group R] [Finite R] [MulAction R (Fin 3)] [FaithfulSMul R (Fin 3)]

abbrev Lin := W (R := R) (I := Fin 3)

def words (z g : Lin (R := R)) : Fin 3 → Lin (R := R) :=
  ![z,g*z*g⁻¹,g^2*z*(g^2)⁻¹]

theorem words_mem (C : Subgroup (Lin (R := R))) (z g : Lin (R := R))
    (hz : z ∈ C) (hg : g ∈ C) (i : Fin 3) : words z g i ∈ C := by
  fin_cases i
  · exact hz
  · exact C.mul_mem (C.mul_mem hg hz) (C.inv_mem hg)
  · exact C.mul_mem (C.mul_mem (C.pow_mem hg 2) hz) (C.inv_mem (C.pow_mem hg 2))

theorem quotientSocle {n : ℕ}
    (lifted : Fin n → BinaryThreeQuartetLiteralSocles.Model (R := R))
    (target : Fin n → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, BinaryThreeQuartetLiteralSocles.action (lifted i) = target i)
    (hfull : Subgroup.closure (Set.range (fun i => (lifted i).right.right)) = ⊤)
    (word : Fin 3 → Lin (R := R))
    (hword : ∀ i, word i ∈ Subgroup.closure (Set.range (fun i => (lifted i).right)))
    (project : Fin 3 → Fin 3)
    (hproject : ∀ (i : Fin 3) (v : Fin 3 → V),
      v * action (word (project i)) v * action ((word (project i))^2) v =
        Pi.mulSingle i (v i))
    (horbit : ∀ (i : Fin 3) (u v : V), u ≠ 1 → v ≠ 1 →
      ∃ m : Fin 3, action ((word i)^m.val) (Pi.mulSingle i u) = Pi.mulSingle i v)
    (htrans : ∀ i j : Fin 3, ∃ r : R, r • i = j)
    (c : R) (i₀ : Fin 3) (hcycle : ∀ j : Fin 3, ∃ m : ℕ, c^m • i₀ = j)
    (hnormal : ∀ N : Subgroup R, N.Normal → MarkedC4.normalGen N ≤ 1)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 3 := by
  let K := Subgroup.closure (Set.range lifted)
  let C := BinaryPlaneWreathNormalGenerators.actualImage K
  have hC : Subgroup.closure (Set.range (fun i => (lifted i).right)) ≤ C := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨closureGenerators lifted j,rfl⟩
  have hw (i : Fin 3) : word i ∈ C := hC (hword i)
  let beta : C →* R := PermutationalWreathProduct.rightHom.comp C.subtype
  have hbeta : Function.Surjective beta := by
    have htop : (⊤ : Subgroup R) ≤ beta.range := by
      rw [← hfull]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j,rfl⟩
      exact ⟨⟨(lifted j).right,hC (Subgroup.subset_closure (Set.mem_range_self j))⟩,rfl⟩
    intro r
    exact htop (Subgroup.mem_top r)
  have hmove : ∀ i j : Fin 3, ∃ q : C, (q : Lin (R := R)).right • i = j := by
    intro i j
    obtain ⟨r,hr⟩ := htrans i j
    obtain ⟨q,hq⟩ := hbeta r
    exact ⟨q,by change beta q • i = j; rw [hq,hr]⟩
  have hirr : IrreducibleAbelianSemidirect.Irreducible (restrictedAction C) := by
    apply functionBlock_irreducible_of_three_term_projection_and_local_orbits
      (restrictedAction C) ?_ ?_ (fun i => ⟨word (project i),hw (project i)⟩) ?_
    · intro i u v hu hv
      obtain ⟨m,hm⟩ := horbit i u v hu hv
      exact ⟨⟨(word i)^m.val,C.pow_mem (hw i) m.val⟩,hm⟩
    · intro i j
      obtain ⟨q,hq⟩ := hmove i j
      refine ⟨q,BinaryPlaneWreathIrreducible.localAction ((q : Lin (R := R)).left j),?_⟩
      intro v
      change action (q : Lin (R := R)) (Pi.mulSingle i v) = _
      rw [action_single,hq]
    · exact hproject
  have htuples := IrreducibleAbelianSemidirectSubgroup.normal_generating_tuples
    BinaryPlaneWreathIrreducible.action K
    (BinaryPlaneWreathIrreducible.action_injective.comp Subtype.val_injective)
    hirr (by omega : 0 < 3)
    (BinaryPlaneWreathNormalGenerators.normal_generating_tuples C hbeta c i₀ hcycle 1 hnormal)
  let f : K →* Equiv.Perm (Fin 12) := BinaryThreeQuartetLiteralSocles.action.comp K.subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) target (Equiv.refl _)
    (closureGenerators_full lifted) hbinding
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) target (Equiv.refl _)
      (closureGenerators_full lifted) hbinding
  exact normal_generating_tuples_of_surjective ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi) htuples
    (finiteGroupSocle _) inferInstance

end SymmetricSubgroupAsymptotics.BinaryThreeQuartetPairedOrbitSocles

end
