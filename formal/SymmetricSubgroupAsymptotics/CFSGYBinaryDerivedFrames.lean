import SymmetricSubgroupAsymptotics.BicoloredInvolutionDerivedBinaryFrames
import SymmetricSubgroupAsymptotics.CFSGYSectionEvenOrder

/-! Two genuine binary subgroups generate the original Y-derived group
for EVERY arm triple of length at least two. Their images generate its
FULL centre quotient. This applies directly to the pinned Fischer and
Baby Monster sections, without any external model identification. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGYBinaryDerivedFrames
open CFSG.Models.YGroups CFSGGeneration CFSGReduction

private abbrev generator (arms : Arms) (i : Node arms) : CFSG.Models.YGroups.Group arms :=
  PresentedGroup.of (rels := relations arms) i

def color (arms : Arms) : Node arms → Bool
  | none => false
  | some p => decide (p.2.val%2=0)

theorem adjacent_colors_ne (arms : Arms) (i j : Node arms) (h : Adjacent arms i j) :
    color arms i≠color arms j := by
  cases i with
  | none =>
    cases j with
    | none => exact False.elim h
    | some q =>
      rcases q with ⟨b,e⟩
      change e.val=0 at h
      simp only [color,h,Nat.zero_mod,decide_true]
      decide
  | some p =>
    rcases p with ⟨a,d⟩
    cases j with
    | none =>
      change d.val=0 at h
      simp only [color,h,Nat.zero_mod,decide_true]
      decide
    | some q =>
      rcases q with ⟨b,e⟩
      intro he
      change decide (d.val%2=0)=decide (e.val%2=0) at he
      have hm : d.val%2=0 ↔ e.val%2=0 := decide_eq_decide.mp he
      rcases h.2 with hs | hs <;> omega

private theorem nonadjacent_commute (arms : Arms) (i j : Node arms)
    (hne : i≠j) (hij : ¬Adjacent arms i j) :
    Commute (generator arms i) (generator arms j) := by
  have hi : (generator arms i)⁻¹=generator arms i :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using y_generator_sq arms i)
  have hj : (generator arms j)⁻¹=generator arms j :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using y_generator_sq arms j)
  have hp : (generator arms i*generator arms j)⁻¹=generator arms i*generator arms j :=
    inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using y_nonadjacent_product_sq arms i j ⟨hne,hij⟩)
  have he : generator arms j*generator arms i=generator arms i*generator arms j := by
    simpa only [mul_inv_rev,hi,hj] using hp
  exact he.symm

theorem same_color_commute (arms : Arms) (i j : Node arms)
    (h : color arms i=color arms j) : Commute (generator arms i) (generator arms j) := by
  by_cases he : i=j
  · subst j
    exact Commute.refl _
  · exact nonadjacent_commute arms i j he (fun hadj => adjacent_colors_ne arms i j hadj h)

private theorem different_arms_commute (arms : Arms) (a b : Fin 3) (hab : a≠b)
    (d e : Fin 2) :
    Commute (generator arms (near arms a d)) (generator arms (near arms b e)) := by
  apply nonadjacent_commute
  · intro he
    have he' : a=b := congrArg (fun q : Node arms =>
      match q with | none => (0 : Fin 3) | some v => v.1) he
    exact hab he'
  · intro h
    exact hab h.1

/-- Actual binary subgroups of the actual original derived group. -/
theorem exists_binary_generating_subgroups (arms : Arms) :
    ∃ U V : Subgroup (commutator (CFSG.Models.YGroups.Group arms)),
      IsPGroup 2 U ∧ IsPGroup 2 V ∧ U⊔V=⊤ := by
  apply BicoloredInvolutionDerivedBinaryFrames.exists_binary_generating_subgroups
    (generator arms) none (color arms) (PresentedGroup.closure_range_of (relations arms))
    (fun i => by simpa only [pow_two] using y_generator_sq arms i)
    (y_abelianization_generators_equal arms) (same_color_commute arms)
    (near arms 0 1) (near arms 0 0) (near arms 1 1) (near arms 2 0)
  · simp [color,near]
  · simp [color,near]
  · simp [color,near]
  · simp [color,near]
  · exact y_adjacent_product_cube arms (near arms 0 1) (near arms 0 0)
      (by simp [Adjacent,near])
  · exact different_arms_commute arms 1 0 (by decide) 1 0
  · exact different_arms_commute arms 2 0 (by decide) 0 1
  · exact different_arms_commute arms 1 2 (by decide) 1 0

/-- No finite ambient Y-group is assumed. Only the literal full-centre
quotient is finite, as inherited at a CFSG-model application. -/
theorem goodSylowPrime (arms : Arms) [Finite (SimpleSection arms)]
    (hCFSG : CFSG.CFSGClassification) : GoodSylowPrime (SimpleSection arms) 2 := by
  obtain ⟨U,V,hU,hV,hgen⟩ := exists_binary_generating_subgroups arms
  let q : commutator (CFSG.Models.YGroups.Group arms) →* SimpleSection arms :=
    QuotientGroup.mk' (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms)))
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  apply goodSylowTwo_of_two_binary_subgroups hCFSG (U.map q) (V.map q) (hU.map q) (hV.map q)
  rw [←Subgroup.map_sup,hgen,Subgroup.map_top_of_surjective q hq]

end SymmetricSubgroupAsymptotics.CFSGYBinaryDerivedFrames
