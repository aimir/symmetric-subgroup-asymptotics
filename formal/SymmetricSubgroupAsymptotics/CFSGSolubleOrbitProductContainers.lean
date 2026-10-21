import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersInterface
import SymmetricSubgroupAsymptotics.CFSGOrdinaryContainerCoverFormula
import SymmetricSubgroupAsymptotics.MarkedC4LiteralSolubleOrbitContainers

/-! An actual labelled soluble cover on all points from actual labelled
transitive covers. Original orbit fibres are encoded by one original-point
label map. All fibre choices have a single shared physical degree budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSolubleOrbitProductContainers
open CFSGSolubleWreathContainers CFSGOrdinaryContainerCoverFormula
open MarkedC4.LiteralSolubleOrbitContainers

/-- Finite products of actual soluble groups are soluble, without a
uniform derived-length hypothesis. The finite sum supplies such a length. -/
theorem finite_pi_isSolvable {I : Type} [Fintype I] (D : I → Type)
    [∀ i,Group (D i)] [∀ i,IsSolvable (D i)] : IsSolvable (∀ i,D i) := by
  choose n hn using fun i => IsSolvable.solvable (G := D i)
  refine ⟨∑ i : I,n i,le_antisymm ?_ bot_le⟩
  intro a ha
  apply Subgroup.mem_bot.mpr
  funext i
  have hm := map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom D i)
    (∑ j : I,n j) ⟨a,ha,rfl⟩
  have hni : n i≤∑ j : I,n j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hmi := derivedSeries_antitone (D i) hni hm
  rw [hn i] at hmi
  exact Subgroup.mem_bot.mp hmi

variable (E : ∀ d : ℕ,TransitiveSolubleContainerCover d) (b : ℕ)

abbrev OrbitProductIndex := Σ label : Fin b → Fin b,
  ∀ i : Fin b,(E (Fintype.card (Fiber label i))).Index

instance orbitProductIndexFinite : Finite (OrbitProductIndex E b) := by
  unfold OrbitProductIndex
  infer_instance

def localGroup (label : Fin b → Fin b)
    (a : ∀ i : Fin b,(E (Fintype.card (Fiber label i))).Index) (i : Fin b) :
    Subgroup (Equiv.Perm (Fiber label i)) :=
  ((E (Fintype.card (Fiber label i))).group (a i)).map
    (Fintype.equivFin (Fiber label i)).symm.permCongrHom.toMonoidHom

theorem localGroup_soluble (label : Fin b → Fin b)
    (a : ∀ i : Fin b,(E (Fintype.card (Fiber label i))).Index) (i : Fin b) :
    IsSolvable (localGroup E b label a i) := by
  letI := (E (Fintype.card (Fiber label i))).soluble (a i)
  let e := (Fintype.equivFin (Fiber label i)).symm.permCongrHom
  let q := ((E (Fintype.card (Fiber label i))).group (a i)).equivMapOfInjective
    e.toMonoidHom e.injective
  exact solvable_of_solvable_injective (f := q.symm.toMonoidHom) q.symm.injective

def productHom (label : Fin b → Fin b)
    (a : ∀ i : Fin b,(E (Fintype.card (Fiber label i))).Index) :
    (∀ i : Fin b,localGroup E b label a i) →* Equiv.Perm (Fin b) :=
  (Equiv.sigmaFiberEquiv label).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sigmaCongrRightHom (Fiber label)).comp
      { toFun := fun g i => (g i).val
        map_one' := rfl
        map_mul' := fun _ _ => rfl })

def productGroup (a : OrbitProductIndex E b) : Subgroup (Equiv.Perm (Fin b)) :=
  (productHom E b a.1 a.2).range

theorem productGroup_soluble (a : OrbitProductIndex E b) : IsSolvable (productGroup E b a) := by
  letI (i : Fin b) : IsSolvable (localGroup E b a.1 a.2 i) := localGroup_soluble E b a.1 a.2 i
  letI : IsSolvable (∀ i : Fin b,localGroup E b a.1 a.2 i) := finite_pi_isSolvable _
  exact solvable_of_surjective (productHom E b a.1 a.2).rangeRestrict_surjective

/-- Every original soluble group lies in an actual product envelope on
those SAME points, not just in a conjugate abstract model. -/
theorem productGroup_covers (G : Subgroup (Equiv.Perm (Fin b))) (hG : IsSolvable G) :
    ∃ a : OrbitProductIndex E b,G≤productGroup E b a := by
  letI : IsSolvable G := hG
  let label := orbitLabel G
  let f := fiberAction G (orbitLabel_invariant G)
  let e (i : Fin b) := Fintype.equivFin (Fiber label i)
  let q (i : Fin b) : G →* Equiv.Perm (Fin (Fintype.card (Fiber label i))) :=
    (e i).permCongrHom.toMonoidHom.comp (f i)
  have hlocal (i : Fin b) : ∃ a : (E (Fintype.card (Fiber label i))).Index,
      (q i).range≤(E (Fintype.card (Fiber label i))).group a := by
    letI : IsSolvable (q i).range := solvable_of_surjective (q i).rangeRestrict_surjective
    have htrans : MulAction.IsPretransitive (q i).range
        (Fin (Fintype.card (Fiber label i))) := by
      constructor
      intro x y
      obtain ⟨g,hg⟩ := orbitLabel_transitive G i ((e i).symm x) ((e i).symm y)
      refine ⟨(q i).rangeRestrict g,?_⟩
      have hh := congrArg (e i) hg
      simpa only [Equiv.apply_symm_apply] using hh
    exact (E (Fintype.card (Fiber label i))).covers (q i).range inferInstance htrans
  choose a ha using hlocal
  refine ⟨⟨label,a⟩,?_⟩
  intro g hg
  let u : ∀ i : Fin b,localGroup E b label a i := fun i =>
    ⟨f i ⟨g,hg⟩,⟨q i ⟨g,hg⟩,ha i ⟨⟨g,hg⟩,rfl⟩,by
      change (e i).symm.permCongr ((e i).permCongr (f i ⟨g,hg⟩))=f i ⟨g,hg⟩
      ext x
      simp⟩⟩
  refine ⟨u,?_⟩
  apply Equiv.ext
  intro x
  rfl

def fullCover : SolubleContainerCover b where
  Index := OrbitProductIndex E b
  finiteIndex := inferInstance
  group := productGroup E b
  soluble := productGroup_soluble E b
  covers := productGroup_covers E b

/-- The exact finite index count exposes every fibre choice. -/
theorem index_card_eq : Nat.card (OrbitProductIndex E b)=
    ∑ label : Fin b → Fin b,∏ i : Fin b,Nat.card ((E (Fintype.card (Fiber label i))).Index) := by
  rw [OrbitProductIndex,Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro label _
  exact Nat.card_pi

/-- One degree budget controls the entire orbit-product menu. A uniform
transitive cost2^(B*d) costs2^(B*b), plus only b^b original labels. -/
theorem index_real_card_le (B : ℝ)
    (hcount : ∀ d : ℕ,d≤b → (Nat.card (E d).Index : ℝ)≤(2 : ℝ)^(B*d)) :
    (Nat.card (OrbitProductIndex E b) : ℝ)≤(b : ℝ)^b*(2 : ℝ)^(B*b) := by
  have hlocal (label : Fin b → Fin b) :
      (∏ i : Fin b,(Nat.card (E (Fintype.card (Fiber label i))).Index : ℝ))≤
        (2 : ℝ)^(B*b) := by
    calc
      _ ≤ ∏ i : Fin b,(2 : ℝ)^(B*Fintype.card (Fiber label i)) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        intro i _
        exact hcount _ (by
          simpa only [Fintype.card_fin] using
            Fintype.card_le_of_injective (fun x : Fiber label i => x.val) Subtype.val_injective)
      _ = _ := by
        rw [←Real.rpow_sum_of_pos (by norm_num : (0 : ℝ)<2),←Finset.mul_sum]
        have hs : (∑ i : Fin b,(Fintype.card (Fiber label i) : ℝ))=(b : ℝ) := by
          have hsN : (∑ i : Fin b,Fintype.card (Fiber label i))=b := by
            simpa only [Fintype.card_sigma,Fintype.card_fin] using
              Fintype.card_congr (Equiv.sigmaFiberEquiv label)
          exact_mod_cast hsN
        rw [hs]
  rw [index_card_eq]
  push_cast
  calc
    _ ≤ ∑ _label : Fin b → Fin b,(2 : ℝ)^(B*b) := Finset.sum_le_sum (fun label _ => hlocal label)
    _ = _ := by simp

end SymmetricSubgroupAsymptotics.CFSGSolubleOrbitProductContainers
