import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4DualPolarConnectivity

/-! Increasing the target intersection in a codimension-one step
FORCES preservation of the previous intersection. Consequently the
maximal-singular graph remains connected while containing any fixed
common subspace. No residual quotient coordinates are required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PolarHyperplane
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem intersection_le_of_adjacent_gain (P L R : Submodule K V) (r : ℕ)
    (hdR : Module.finrank K R = r) (hcap : Module.finrank K ↥(P ⊓ R) + 1 = r)
    (hgain : Module.finrank K ↥(P ⊓ L) + 1 ≤ Module.finrank K ↥(R ⊓ L)) : P ⊓ L ≤ R := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (R ⊓ L) (R ⊓ P)
  have hs := Submodule.finrank_mono
    (sup_le inf_le_left inf_le_left : (R ⊓ L) ⊔ (R ⊓ P) ≤ R)
  rw [hdR] at hs
  have hc := hcap
  rw [inf_comm] at hc
  have hdim : Module.finrank K ↥(P ⊓ L) ≤ Module.finrank K ↥((R ⊓ L) ⊓ (R ⊓ P)) := by omega
  have hle : (R ⊓ L) ⊓ (R ⊓ P) ≤ P ⊓ L :=
    fun _ hx => ⟨hx.2.2, hx.1.2⟩
  have he : (R ⊓ L) ⊓ (R ⊓ P) = P ⊓ L := Submodule.eq_of_le_of_finrank_le hle hdim
  exact he.symm.le.trans (inf_le_left.trans inf_le_left)

def ContainingMaximalSingular (Q : QuadraticForm K V) (r : ℕ) (U : Submodule K V) :=
  {P : MaximalSingular Q r // U ≤ P.val}

theorem fixed_space_dual_polar_connected (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (U : Submodule K V) (P L : ContainingMaximalSingular Q r U) :
    Relation.ReflTransGen (fun A B : ContainingMaximalSingular Q r U => DualAdjacent Q r A.val B.val) P L := by
  suffices hall : ∀ n, ∀ P : ContainingMaximalSingular Q r U,
      r - Module.finrank K ↥(P.val.val ⊓ L.val.val) = n →
        Relation.ReflTransGen (fun A B : ContainingMaximalSingular Q r U => DualAdjacent Q r A.val B.val) P L by
    exact hall _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hn
    by_cases he : P = L
    · subst P
      exact Relation.ReflTransGen.refl
    · have hnot : ¬ L.val.val ≤ P.val.val := by
        intro h
        have hh : L.val.val = P.val.val := Submodule.eq_of_le_of_finrank_le h
          (by rw [P.val.property.1, L.val.property.1])
        exact he (Subtype.ext (Subtype.ext hh.symm))
      obtain ⟨u, huL, huP⟩ := Set.not_subset.mp hnot
      obtain ⟨R, hRP, hdR, hzR, hcap, hgain⟩ := dual_polar_replacement_step Q P.val.val L.val.val r
        P.val.property.1 (maximalSingular_self_orthogonal Q hQ r hV P.val)
        P.val.property.2 L.val.property.2 u huL huP
      have hUR : U ≤ R := (le_inf P.property L.property).trans
        (intersection_le_of_adjacent_gain P.val.val L.val.val R r hdR hcap hgain)
      let R' : ContainingMaximalSingular Q r U := ⟨⟨R, hdR, hzR⟩, hUR⟩
      have hadj : DualAdjacent Q r P.val R'.val :=
        ⟨fun hh => hRP (congrArg Subtype.val hh).symm, hcap⟩
      have hhi := Submodule.finrank_mono (inf_le_left : R ⊓ L.val.val ≤ R)
      rw [hdR] at hhi
      have hlt : r - Module.finrank K ↥(R ⊓ L.val.val) < n := by
        rw [← hn]
        omega
      have hstep : Relation.ReflTransGen
          (fun A B : ContainingMaximalSingular Q r U => DualAdjacent Q r A.val B.val) P R' :=
        Relation.ReflTransGen.single hadj
      exact hstep.trans (ih _ hlt R' rfl)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PolarHyperplane
