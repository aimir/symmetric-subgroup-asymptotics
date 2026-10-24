import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-! An ambient conjugacy fibre inside an actual point stabilizer is
controlled by centralizer orbits on fixed points of the actual ambient
point orbit. No normality of the stabilizer and no form-orbit estimate
is assumed. The conjugator criterion retains both chosen conjugators. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.StabilizerConjugacyFibreOrbit

variable {G X : Type*} [Group G] [MulAction G X]

def fixedOrbit (b : X) (a : MulAction.stabilizer G b) : Set X :=
  {x | x ∈ MulAction.orbit G b ∧ (a : G) • x = x}

abbrev centralizer (b : X) (a : MulAction.stabilizer G b) : Subgroup G :=
  Subgroup.centralizer ({(a : G)} : Set G)

instance centralizerFixedOrbitAction (b : X) (a : MulAction.stabilizer G b) :
    MulAction (centralizer b a) (fixedOrbit b a) where
  smul c x := ⟨(c : G) • x.val, by
    refine ⟨?_, ?_⟩
    · obtain ⟨g, hg⟩ := x.property.1
      change g • b = x.val at hg
      refine ⟨(c : G) * g, ?_⟩
      change ((c : G) * g) • b = (c : G) • x.val
      rw [mul_smul, hg]
    · have hc : (a : G) * (c : G) = (c : G) * (a : G) :=
        (Subgroup.mem_centralizer_iff.mp c.property) _ rfl
      calc
        (a : G) • ((c : G) • x.val) = ((a : G) * (c : G)) • x.val :=
          (mul_smul _ _ _).symm
        _ = ((c : G) * (a : G)) • x.val := congrArg (fun g : G => g • x.val) hc
        _ = (c : G) • x.val := by rw [mul_smul, x.property.2]⟩
  one_smul x := by
    apply Subtype.ext
    exact one_smul G x.val
  mul_smul c d x := by
    apply Subtype.ext
    exact mul_smul (c : G) (d : G) x.val

def conjugatorPoint (b : X) (a : MulAction.stabilizer G b) (g : G)
    (hg : g * (a : G) * g⁻¹ ∈ MulAction.stabilizer G b) : fixedOrbit b a :=
  ⟨g⁻¹ • b, ⟨g⁻¹, rfl⟩, by
    have h := congrArg (fun x : X => g⁻¹ • x)
      (show (g * (a : G) * g⁻¹) • b = b from hg)
    simpa only [mul_smul, inv_smul_smul] using h⟩

theorem conjugate_isConj_iff_centralizer_orbit
    (b : X) (a : MulAction.stabilizer G b) (g h : G)
    (hg : g * (a : G) * g⁻¹ ∈ MulAction.stabilizer G b)
    (hh : h * (a : G) * h⁻¹ ∈ MulAction.stabilizer G b) :
    IsConj (⟨g * (a : G) * g⁻¹, hg⟩ : MulAction.stabilizer G b)
      ⟨h * (a : G) * h⁻¹, hh⟩ ↔
      ∃ c : centralizer b a,
        c • conjugatorPoint b a g hg = conjugatorPoint b a h hh := by
  constructor
  · intro ht
    obtain ⟨t, ht⟩ := isConj_iff.mp ht
    have ht' : (t : G) * (g * (a : G) * g⁻¹) * (t : G)⁻¹ =
        h * (a : G) * h⁻¹ := congrArg (fun z : MulAction.stabilizer G b => (z : G)) ht
    let c : G := h⁻¹ * (t : G) * g
    have hca : c * (a : G) * c⁻¹ = (a : G) := by
      calc
        _ = h⁻¹ * ((t : G) * (g * (a : G) * g⁻¹) * (t : G)⁻¹) * h := by
          dsimp only [c]
          group
        _ = h⁻¹ * (h * (a : G) * h⁻¹) * h := by rw [ht']
        _ = (a : G) := by group
    have hc : c ∈ centralizer b a := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      have hz' : z = (a : G) := Set.mem_singleton_iff.mp hz
      subst z
      have hm := congrArg (fun z : G => z * c) hca
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm.symm
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    change (h⁻¹ * (t : G) * g) • (g⁻¹ • b) = h⁻¹ • b
    have htb : (t : G) • b = b := t.property
    simp only [mul_smul, smul_inv_smul, htb]
  · rintro ⟨c, hc⟩
    have hc' : (c : G) • (g⁻¹ • b) = h⁻¹ • b :=
      congrArg (fun x : fixedOrbit b a => (x : X)) hc
    let t : G := h * (c : G) * g⁻¹
    have ht : t ∈ MulAction.stabilizer G b := by
      change (h * (c : G) * g⁻¹) • b = b
      rw [mul_smul, mul_smul, hc', smul_inv_smul]
    apply isConj_iff.mpr
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    change t * (g * (a : G) * g⁻¹) * t⁻¹ = h * (a : G) * h⁻¹
    have hca : (a : G) * (c : G) = (c : G) * (a : G) :=
      (Subgroup.mem_centralizer_iff.mp c.property) _ rfl
    have hcc : (c : G) * (a : G) * (c : G)⁻¹ = (a : G) := by
      rw [← hca, mul_assoc, mul_inv_cancel, mul_one]
    calc
      _ = h * ((c : G) * (a : G) * (c : G)⁻¹) * h⁻¹ := by
        dsimp only [t]
        group
      _ = _ := by rw [hcc]

def classFibre (b : X) (a : MulAction.stabilizer G b) :=
  {c : ConjClasses (MulAction.stabilizer G b) //
    ConjClasses.map (MulAction.stabilizer G b).subtype c = ConjClasses.mk (a : G)}

private theorem exists_conjugator (b : X) (a : MulAction.stabilizer G b)
    (c : classFibre b a) :
    ∃ g : G, ∃ hg : g * (a : G) * g⁻¹ ∈ MulAction.stabilizer G b,
      ConjClasses.mk (⟨g * (a : G) * g⁻¹, hg⟩ : MulAction.stabilizer G b) = c.val := by
  obtain ⟨y, hy⟩ := ConjClasses.mk_surjective c.val
  have ha : ConjClasses.mk (y : G) = ConjClasses.mk (a : G) := by
    have hc := c.property
    rw [← hy] at hc
    exact hc
  obtain ⟨g, hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ha).symm
  have hmem : g * (a : G) * g⁻¹ ∈ MulAction.stabilizer G b := by
    rw [hg]
    exact y.property
  refine ⟨g, hmem, ?_⟩
  have he : (⟨g * (a : G) * g⁻¹, hmem⟩ : MulAction.stabilizer G b) = y := Subtype.ext hg
  exact (congrArg ConjClasses.mk he).trans hy

private def chosenConjugator (b : X) (a : MulAction.stabilizer G b)
    (c : classFibre b a) : G := (exists_conjugator b a c).choose

private theorem chosenConjugator_mem (b : X) (a : MulAction.stabilizer G b)
    (c : classFibre b a) :
    chosenConjugator b a c * (a : G) * (chosenConjugator b a c)⁻¹ ∈
      MulAction.stabilizer G b := (exists_conjugator b a c).choose_spec.choose

private theorem chosenConjugator_class (b : X) (a : MulAction.stabilizer G b)
    (c : classFibre b a) :
    ConjClasses.mk (⟨chosenConjugator b a c * (a : G) * (chosenConjugator b a c)⁻¹,
      chosenConjugator_mem b a c⟩ : MulAction.stabilizer G b) = c.val :=
  (exists_conjugator b a c).choose_spec.choose_spec

def fibreToCentralizerOrbits (b : X) (a : MulAction.stabilizer G b) :
    classFibre b a → Quotient (MulAction.orbitRel (centralizer b a) (fixedOrbit b a)) :=
  fun c => Quotient.mk''
    (conjugatorPoint b a (chosenConjugator b a c) (chosenConjugator_mem b a c))

theorem fibreToCentralizerOrbits_injective (b : X) (a : MulAction.stabilizer G b) :
    Function.Injective (fibreToCentralizerOrbits b a) := by
  intro c d he
  have horbit := Quotient.exact he
  obtain ⟨t, ht⟩ := horbit
  have hconj := (conjugate_isConj_iff_centralizer_orbit b a
    (chosenConjugator b a d) (chosenConjugator b a c)
    (chosenConjugator_mem b a d) (chosenConjugator_mem b a c)).mpr ⟨t, ht⟩
  apply Subtype.ext
  exact (chosenConjugator_class b a c).symm.trans
    ((ConjClasses.mk_eq_mk_iff_isConj.mpr hconj.symm).trans (chosenConjugator_class b a d))

theorem fibre_card_le_centralizer_orbits [Finite X]
    (b : X) (a : MulAction.stabilizer G b) :
    Nat.card (classFibre b a) ≤
      Nat.card (Quotient (MulAction.orbitRel (centralizer b a) (fixedOrbit b a))) :=
  Nat.card_le_card_of_injective (fibreToCentralizerOrbits b a)
    (fibreToCentralizerOrbits_injective b a)

end SymmetricSubgroupAsymptotics.StabilizerConjugacyFibreOrbit
