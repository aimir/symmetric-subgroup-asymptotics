import SymmetricSubgroupAsymptotics.RepeatedC3TailExtraction

/-!
# Simultaneous physical chart for all regular C3 orbits

Every literal regular `C3` orbit is kept as one original ternary occurrence.
All remaining literal orbits are merged into one invariant tail block.  The
chart below is an equivalence of the complete original point set; it neither
points a preferred regular orbit nor replaces the tail action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace RepeatedC3TailPhysical

open RepeatedC3TailExtraction RepeatedC3TailProfile

variable {X : Type} [Fintype X] (G : Subgroup (Equiv.Perm X))

def regularCount : ℕ := Nat.card (RegularOrbit G)
def tailDegree : ℕ := Nat.card (TailPoint G)

def regularIndex : Fin (regularCount G) ≃ RegularOrbit G :=
  (Finite.equivFin _).symm

def regularChart (j : Fin (regularCount G)) :
    TernaryCyclic ≃ (regularIndex G j).1.orbit :=
  Classical.choose (regularOrbit_chart G (regularIndex G j))

theorem regularChart_image (j : Fin (regularCount G)) :
    relabelSubgroup (regularChart G j) ternaryRegularAction =
      OrbitProfileFromOrbits.orbitImage G (regularIndex G j).1 :=
  Classical.choose_spec (regularOrbit_chart G (regularIndex G j))

def tailIndex : Fin (tailDegree G) ≃ TailPoint G :=
  (Finite.equivFin _).symm

private theorem orbit_eq_of_mem
    {o p : OrbitProfileFromOrbits.Orbit G} {x : X}
    (ho : x ∈ o.orbit) (hp : x ∈ p.orbit) : o = p :=
  ((MulAction.orbitRel.Quotient.mem_orbit).mp ho).symm.trans
    ((MulAction.orbitRel.Quotient.mem_orbit).mp hp)

private theorem tailPoint_forget_injective :
    Function.Injective (fun z : TailPoint G => z.2.1) := by
  intro a b hab
  let E := (MulAction.selfEquivSigmaOrbits' G X).symm
  have hall :
      (⟨a.1.1, a.2⟩ : Σ o : OrbitProfileFromOrbits.Orbit G, o.orbit) =
        ⟨b.1.1, b.2⟩ := by
    apply E.injective
    exact hab
  have htag : a.1 = b.1 :=
    Subtype.ext (congrArg Sigma.fst hall)
  exact Sigma.ext htag (Sigma.mk.inj_iff.mp hall).2

/-- Forget the simultaneous regular/tail coordinates into the original
point set. -/
def pointMap : ModelPoints (regularCount G) (tailDegree G) → X
  | ⟨.inl _, j, x⟩ => (regularChart G j x : X)
  | ⟨.inr _, _, x⟩ => (tailIndex G x).2.1

private theorem pointMap_injective : Function.Injective (pointMap G) := by
  rintro ⟨i,j,x⟩ ⟨k,l,y⟩ h
  cases i with
  | inl ui =>
      cases ui
      cases k with
      | inl uk =>
          cases uk
          change ((regularChart G j x : (regularIndex G j).1.orbit) : X) =
            ((regularChart G l y : (regularIndex G l).1.orbit) : X) at h
          have horbit : (regularIndex G j).1 = (regularIndex G l).1 :=
            orbit_eq_of_mem G (regularChart G j x).2
              (h ▸ (regularChart G l y).2)
          have hj : j = l := by
            apply (regularIndex G).injective
            apply Subtype.ext
            exact horbit
          subst l
          have hxy : x = y := (regularChart G j).injective (Subtype.ext h)
          subst y
          rfl
      | inr uk =>
          cases uk
          change ((regularChart G j x : (regularIndex G j).1.orbit) : X) =
            (tailIndex G y).2.1 at h
          have horbit : (regularIndex G j).1 = (tailIndex G y).1.1 :=
            orbit_eq_of_mem G (regularChart G j x).2
              (h ▸ (tailIndex G y).2.2)
          exact False.elim ((tailIndex G y).1.2 (horbit ▸ (regularIndex G j).2))
  | inr ui =>
      cases ui
      cases k with
      | inl uk =>
          cases uk
          change (tailIndex G x).2.1 =
            ((regularChart G l y : (regularIndex G l).1.orbit) : X) at h
          have horbit : (tailIndex G x).1.1 = (regularIndex G l).1 :=
            orbit_eq_of_mem G (tailIndex G x).2.2
              (h ▸ (regularChart G l y).2)
          exact False.elim ((tailIndex G x).1.2 (horbit ▸ (regularIndex G l).2))
      | inr uk =>
          cases uk
          change (tailIndex G x).2.1 = (tailIndex G y).2.1 at h
          have htail : tailIndex G x = tailIndex G y :=
            tailPoint_forget_injective G h
          have hxy : x = y := (tailIndex G).injective htail
          subst y
          have hjl : j = l :=
            (fin_eq_tailIndex (regularCount G) j).trans
              (fin_eq_tailIndex (regularCount G) l).symm
          subst l
          rfl

private theorem pointMap_surjective : Function.Surjective (pointMap G) := by
  intro x
  let o : OrbitProfileFromOrbits.Orbit G := Quotient.mk'' x
  have hx : x ∈ o.orbit :=
    (MulAction.orbitRel.Quotient.mem_orbit).mpr rfl
  by_cases hregular : IsRegularC3Orbit G o
  · let r : RegularOrbit G := ⟨o,hregular⟩
    obtain ⟨j,hj⟩ := (regularIndex G).surjective r
    let z : (regularIndex G j).1.orbit := ⟨x, by
      rw [hj]
      exact hx⟩
    let a : TernaryCyclic := (regularChart G j).symm z
    refine ⟨⟨.inl PUnit.unit,j,a⟩, ?_⟩
    change ((regularChart G j) a : X) = x
    have ha := congrArg Subtype.val
      ((regularChart G j).apply_symm_apply z)
    simpa only [a] using ha
  · let r : TailOrbit G := ⟨o,hregular⟩
    let z : TailPoint G := ⟨r,⟨x,hx⟩⟩
    let a : Fin (tailDegree G) := (tailIndex G).symm z
    refine ⟨⟨.inr PUnit.unit,
      RepeatedC3TailProfile.tailIndex (regularCount G), a⟩, ?_⟩
    change ((tailIndex G) a).2.1 = x
    have ha := congrArg (fun q : TailPoint G => q.2.1)
      ((tailIndex G).apply_symm_apply z)
    simpa only [a, z] using ha

/-- The complete physical chart with every regular triple retained and the
literal complementary action merged into one block. -/
def chart : ModelPoints (regularCount G) (tailDegree G) ≃ X :=
  Equiv.ofBijective (pointMap G) ⟨pointMap_injective G, pointMap_surjective G⟩

@[simp] theorem chart_regular
    (j : Fin (regularCount G)) (x : TernaryCyclic) :
    chart G ⟨.inl PUnit.unit,j,x⟩ = (regularChart G j x : X) := rfl

@[simp] theorem chart_tail
    (j : Fin (multiplicity (regularCount G) (.inr PUnit.unit)))
    (x : Fin (tailDegree G)) :
    chart G ⟨.inr PUnit.unit,j,x⟩ = (tailIndex G x).2.1 := rfl

/-- The action on one regular triple, written in its literal regular-C3
coordinates. -/
def regularCoordinate (j : Fin (regularCount G)) :
    G →* ternaryRegularAction where
  toFun h := ⟨(regularChart G j).symm.permCongr
      (MulAction.toPermHom G (regularIndex G j).1.orbit h), by
    have himage :
        MulAction.toPermHom G (regularIndex G j).1.orbit h ∈
          OrbitProfileFromOrbits.orbitImage G (regularIndex G j).1 :=
      ⟨h,rfl⟩
    rw [← regularChart_image G j] at himage
    exact (mem_relabelSubgroup (regularChart G j) ternaryRegularAction _).mp
      himage⟩
  map_one' := by
    apply Subtype.ext
    change (regularChart G j).symm.permCongr
        (MulAction.toPermHom G (regularIndex G j).1.orbit 1) = 1
    rw [map_one (MulAction.toPermHom G (regularIndex G j).1.orbit)]
    exact map_one (regularChart G j).symm.permCongrHom
  map_mul' h k := by
    apply Subtype.ext
    change (regularChart G j).symm.permCongr
        (MulAction.toPermHom G (regularIndex G j).1.orbit (h * k)) =
      (regularChart G j).symm.permCongr
          (MulAction.toPermHom G (regularIndex G j).1.orbit h) *
        (regularChart G j).symm.permCongr
          (MulAction.toPermHom G (regularIndex G j).1.orbit k)
    rw [map_mul (MulAction.toPermHom G (regularIndex G j).1.orbit)]
    exact map_mul (regularChart G j).symm.permCongrHom _ _

/-- The literal tail action, relabelled by its simultaneous finite index. -/
def tailCoordinate : G →* Equiv.Perm (Fin (tailDegree G)) where
  toFun h := ((tailIndex G).symm.permCongrHom.toMonoidHom.comp
    (tailRepresentation G)) h
  map_one' := map_one _
  map_mul' h k := map_mul _ h k

/-- Every original group element written in all regular-triple coordinates
and in the one retained tail coordinate. -/
def profileHom : G →* Product (regularCount G) (tailDegree G) where
  toFun h i := by
    cases i with
    | inl u =>
        cases u
        exact fun j => regularCoordinate G j h
    | inr u =>
        cases u
        exact fun _ => ⟨tailCoordinate G h, by simp [action]⟩
  map_one' := by
    funext i j
    cases i with
    | inl u =>
        cases u
        change regularCoordinate G j 1 = 1
        exact map_one (regularCoordinate G j)
    | inr u =>
        cases u
        apply Subtype.ext
        exact map_one (tailCoordinate G)
  map_mul' h k := by
    funext i j
    cases i with
    | inl u =>
        cases u
        change regularCoordinate G j (h * k) = _
        exact map_mul (regularCoordinate G j) h k
    | inr u =>
        cases u
        apply Subtype.ext
        exact map_mul (tailCoordinate G) h k

/-- Pointwise compatibility of the simultaneous chart with the product
action. -/
theorem chart_action (h : G)
    (z : ModelPoints (regularCount G) (tailDegree G)) :
    chart G
        (orbitProfileProductAction (RepeatedC3TailProfile.multiplicity (regularCount G))
          (action (tailDegree G)) (profileHom G h) z) =
      h.1 (chart G z) := by
  rcases z with ⟨i,j,x⟩
  cases i with
  | inl u =>
      cases u
      change pointMap G
          ⟨.inl PUnit.unit,j,
            ((regularCoordinate G j h : ternaryRegularAction) :
              Equiv.Perm TernaryCyclic) x⟩ =
        h.1 (pointMap G ⟨.inl PUnit.unit,j,x⟩)
      change (regularChart G j)
          (((regularChart G j).symm.permCongr
            (MulAction.toPermHom G (regularIndex G j).1.orbit h)) x) =
        h.1 (regularChart G j x)
      simp only [Equiv.permCongr_apply, Equiv.symm_symm,
        Equiv.apply_symm_apply]
      rfl
  | inr u =>
      cases u
      change pointMap G ⟨.inr PUnit.unit,j,(tailCoordinate G h) x⟩ =
        h.1 (pointMap G ⟨.inr PUnit.unit,j,x⟩)
      change (tailIndex G)
          (((tailIndex G).symm.permCongr (tailRepresentation G h)) x) |>.2.1 =
        h.1 ((tailIndex G x).2.1)
      simp only [Equiv.permCongr_apply, Equiv.symm_symm]
      rw [Equiv.apply_symm_apply]
      rfl

/-- The product-coordinate subgroup representing the original physical
subgroup. -/
def modelSubgroup : Subgroup (Product (regularCount G) (tailDegree G)) :=
  (profileHom G).range

/-- Mapping the literal coordinate subgroup to the model point set is
exactly the original subgroup conjugated by the inverse physical chart. -/
theorem modelSubgroup_action :
    (modelSubgroup G).map
        (orbitProfileProductAction (RepeatedC3TailProfile.multiplicity (regularCount G))
          (action (tailDegree G))) =
      relabelSubgroup (chart G).symm G := by
  ext p
  constructor
  · rintro ⟨q,⟨h,rfl⟩,rfl⟩
    apply (mem_relabelSubgroup (chart G).symm G _).mpr
    change (chart G).permCongr
        (orbitProfileProductAction (RepeatedC3TailProfile.multiplicity (regularCount G))
          (action (tailDegree G)) (profileHom G h)) ∈ G
    have he : (chart G).permCongr
        (orbitProfileProductAction (RepeatedC3TailProfile.multiplicity (regularCount G))
          (action (tailDegree G)) (profileHom G h)) = h.1 := by
      apply Equiv.ext
      intro x
      obtain ⟨z,rfl⟩ := (chart G).surjective x
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
      exact chart_action G h z
    rw [he]
    exact h.2
  · intro hp
    have hp' := (mem_relabelSubgroup (chart G).symm G p).mp hp
    let h : G := ⟨(chart G).permCongr p, hp'⟩
    refine ⟨profileHom G h, ⟨h,rfl⟩, ?_⟩
    apply ((chart G).permCongr).injective
    apply Equiv.ext
    intro x
    obtain ⟨z,rfl⟩ := (chart G).surjective x
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact (chart_action G h z).trans (by
      simp only [h, Equiv.permCongr_apply, Equiv.symm_apply_apply])

/-- The relabelled tail representation has exactly the literal tail image. -/
theorem tailCoordinate_range :
    (tailCoordinate G).range =
      relabelSubgroup (tailIndex G).symm (tailImage G) := by
  ext p
  constructor
  · rintro ⟨h,rfl⟩
    apply (mem_relabelSubgroup (tailIndex G).symm (tailImage G) _).mpr
    change (tailIndex G).permCongr ((tailCoordinate G) h) ∈ tailImage G
    change (tailIndex G).permCongr
        ((tailIndex G).symm.permCongr (tailRepresentation G h)) ∈ tailImage G
    have he : (tailIndex G).permCongr
        ((tailIndex G).symm.permCongr (tailRepresentation G h)) =
          tailRepresentation G h := by
      apply Equiv.ext
      intro x
      simp
    rw [he]
    exact ⟨h,rfl⟩
  · intro hp
    have hp' :=
      (mem_relabelSubgroup (tailIndex G).symm (tailImage G) p).mp hp
    obtain ⟨h,hh⟩ := hp'
    refine ⟨h, ?_⟩
    apply ((tailIndex G).permCongr).injective
    have he : (tailIndex G).permCongr
        ((tailCoordinate G) h) = tailRepresentation G h := by
      apply Equiv.ext
      intro x
      simp [tailCoordinate]
    rw [he]
    simpa only [Equiv.symm_symm] using hh

/-- Projecting the simultaneous physical subgroup to the retained tail is
the literal tail image, with only the finite index chart changed. -/
theorem modelSubgroup_tail :
    (((modelSubgroup G).map
        (sourceEquiv (regularCount G) (tailDegree G)).toMonoidHom).map
          (MonoidHom.snd (TernaryProductGraphBound.Elementary (regularCount G))
            (Equiv.Perm (Fin (tailDegree G))))) =
      relabelSubgroup (tailIndex G).symm (tailImage G) := by
  rw [← tailCoordinate_range G]
  ext p
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨q,hq,rfl⟩ := hz
    obtain ⟨h,rfl⟩ := hq
    exact ⟨h,rfl⟩
  · rintro ⟨h,rfl⟩
    refine ⟨sourceEquiv (regularCount G) (tailDegree G) (profileHom G h), ?_, ?_⟩
    · exact ⟨profileHom G h, ⟨h,rfl⟩, rfl⟩
    · rfl

/-- Once natural-A4 orbits are excluded, the actual simultaneous physical
subgroup satisfies the sharp retained-tail rank cap. -/
theorem modelSubgroup_tailRankCapped
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hnoA4 : ∀ o : OrbitProfileFromOrbits.Orbit G,
      ¬ IsNaturalA4Action (OrbitProfileFromOrbits.orbitImage G o) o.orbit) :
    TailRankCapped (regularCount G) (2 * tailDegree G / 9) (tailDegree G)
      (modelSubgroup G) := by
  unfold TailRankCapped TernaryProductGraphBound.TailRankCapped
  rw [TernaryProductGraphBound.tail_of_classification, modelSubgroup_tail G]
  have hrank := ternaryCharacterRank_noSmallOrbits hChief hPrimitive h18
    (tailImage G) (tailImage_noSmallOrbits G hnoA4)
  have hcongr : ternaryCharacterRank
      (relabelSubgroup (tailIndex G).symm (tailImage G)) =
        ternaryCharacterRank (tailImage G) := by
    exact (ternaryCharacterRank_congr
      ((tailImage G).equivMapOfInjective
        (tailIndex G).symm.permCongrHom.toMonoidHom
        (tailIndex G).symm.permCongr.injective)).symm
  change ternaryCharacterRank
      (relabelSubgroup (tailIndex G).symm (tailImage G)) ≤
        2 * tailDegree G / 9
  rw [hcongr]
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 9)).2 (by
    simpa only [tailDegree, ternaryCharacterRank, Nat.mul_comm] using hrank)

/-- A literal `3/20` capacity on every normal pair in every retained tail
orbit gives the sharp simultaneous tail cap.  This is the form used after
the complete degree-three packet has been split from the pre-E7 residual. -/
theorem modelSubgroup_tailRankCapped_threeTwentieths
    (hcap : ∀ (q : OrbitProfileFromOrbits.Orbit (tailImage G))
      (N : Subgroup (OrbitProfileFromOrbits.orbitImage (tailImage G) q))
      (hN : N.Normal),
        letI := hN
        20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
          3 * Nat.card q.orbit) :
    TailRankCapped (regularCount G) (3 * tailDegree G / 20) (tailDegree G)
      (modelSubgroup G) := by
  unfold TailRankCapped TernaryProductGraphBound.TailRankCapped
  rw [TernaryProductGraphBound.tail_of_classification, modelSubgroup_tail G]
  have hrank := ternaryCharacterRank_actualOrbit_three_twentieths
    (tailImage G) hcap
  have hcongr : ternaryCharacterRank
      (relabelSubgroup (tailIndex G).symm (tailImage G)) =
        ternaryCharacterRank (tailImage G) := by
    exact (ternaryCharacterRank_congr
      ((tailImage G).equivMapOfInjective
        (tailIndex G).symm.permCongrHom.toMonoidHom
        (tailIndex G).symm.permCongr.injective)).symm
  change ternaryCharacterRank
      (relabelSubgroup (tailIndex G).symm (tailImage G)) ≤
        3 * tailDegree G / 20
  rw [hcongr]
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 20)).2 (by
    simpa only [tailDegree, ternaryCharacterRank, Nat.mul_comm] using hrank)

/-- The physical point degree splits exactly into all retained regular
triples and the literal complementary tail. -/
theorem degree_eq :
    3 * regularCount G + tailDegree G = Fintype.card X := by
  have hcard := Fintype.card_congr (chart G)
  have hternary : Fintype.card TernaryCyclic = 3 := by
    norm_num [TernaryCyclic]
  calc
    3 * regularCount G + tailDegree G =
        ∑ i, RepeatedC3TailProfile.multiplicity (regularCount G) i *
          Fintype.card (points (tailDegree G) i) := by
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, points,
        RepeatedC3TailProfile.multiplicity, one_mul]
      have hleft : 3 * regularCount G =
          regularCount G * Fintype.card TernaryCyclic := by
        calc
          3 * regularCount G = regularCount G * 3 := Nat.mul_comm _ _
          _ = regularCount G * Fintype.card TernaryCyclic :=
            congrArg (fun q : ℕ => regularCount G * q) hternary.symm
      exact congrArg₂ (fun a b : ℕ => a + b)
        hleft
        (Fintype.card_fin (tailDegree G)).symm
    _ = Fintype.card (ModelPoints (regularCount G) (tailDegree G)) := by
      rw [Fintype.card_sigma]
      simp only [OrbitProfilePoints, Fintype.card_prod, Fintype.card_fin]
    _ = Fintype.card X := hcard

/-- A physical group with at least one literal regular triple and no natural
A4 orbit belongs to the exact original-weight assembled profile with its
sharp tail cap. -/
noncomputable def assembled
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hnoA4 : ∀ o : OrbitProfileFromOrbits.Orbit G,
      ¬ IsNaturalA4Action (OrbitProfileFromOrbits.orbitImage G o) o.orbit) :
    AssembledOrbitProfileOn
      (modelPredicate (regularCount G) (2 * tailDegree G / 9) (tailDegree G)) X := by
  let H := modelSubgroup G
  let K := H.map
    (orbitProfileProductAction
      (RepeatedC3TailProfile.multiplicity (regularCount G))
      (action (tailDegree G)))
  refine ⟨G, chart G, K, ?_, ?_⟩
  · exact ⟨H, modelSubgroup_tailRankCapped G hChief hPrimitive h18 hnoA4, rfl⟩
  · dsimp only [K, H]
    rw [modelSubgroup_action G]
    exact relabelSubgroup_symm (chart G).symm G

/-- The same exact original-weight physical assembly under the sharper
`3/20` retained-tail capacity. -/
noncomputable def assembled_threeTwentieths
    (hcap : ∀ (q : OrbitProfileFromOrbits.Orbit (tailImage G))
      (N : Subgroup (OrbitProfileFromOrbits.orbitImage (tailImage G) q))
      (hN : N.Normal),
        letI := hN
        20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
          3 * Nat.card q.orbit) :
    AssembledOrbitProfileOn
      (modelPredicate (regularCount G) (3 * tailDegree G / 20)
        (tailDegree G)) X := by
  let H := modelSubgroup G
  let K := H.map
    (orbitProfileProductAction
      (RepeatedC3TailProfile.multiplicity (regularCount G))
      (action (tailDegree G)))
  refine ⟨G, chart G, K, ?_, ?_⟩
  · exact ⟨H, modelSubgroup_tailRankCapped_threeTwentieths G hcap, rfl⟩
  · dsimp only [K, H]
    rw [modelSubgroup_action G]
    exact relabelSubgroup_symm (chart G).symm G

theorem regularCount_pos
    (o : OrbitProfileFromOrbits.Orbit G) (ho : IsRegularC3Orbit G o) :
    0 < regularCount G := by
  letI : Nonempty (RegularOrbit G) := ⟨⟨o,ho⟩⟩
  exact Nat.card_pos

end RepeatedC3TailPhysical
end SymmetricSubgroupAsymptotics

end
