import SymmetricSubgroupAsymptotics.GaussianCount

/-!
# A labelled disjoint-pair lower bound

Each binary vector translates the two points in each of the first `n / 2`
labelled pairs. The action fixes points outside those pairs. Taking the image
of each actual subspace gives distinct actual subgroups of the symmetric
group, uniformly in even and odd degree.

This proves a foundational lower bound only. It does not count the full
critical family, provide its coefficient normalization, or prove T1.
-/

set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The literal labelled pairs: `(i,b)` occupies point `2*i + b.val`. -/
def binaryPairEmbedding (n : ℕ) : (Fin (halfDegree n) × ZMod 2) ↪ Fin n where
  toFun p := ⟨2 * p.1.val + p.2.val, by
    have hi := p.1.isLt
    have hb := ZMod.val_lt p.2
    dsimp [halfDegree] at hi
    omega⟩
  inj' := by
    intro p q hpq
    have h := congrArg Fin.val hpq
    have hp := ZMod.val_lt p.2
    have hq := ZMod.val_lt q.2
    dsimp at h
    apply Prod.ext
    · apply Fin.ext
      omega
    · apply ZMod.val_injective 2
      omega

@[simp] theorem binaryPairEmbedding_val (n : ℕ) (p : Fin (halfDegree n) × ZMod 2) :
    (binaryPairEmbedding n p).val = 2 * p.1.val + p.2.val := rfl

theorem binaryPairEmbedding_val_lt (n : ℕ) (p : Fin (halfDegree n) × ZMod 2) :
    (binaryPairEmbedding n p).val < 2 * halfDegree n := by
  have hi := p.1.isLt
  have hb := ZMod.val_lt p.2
  rw [binaryPairEmbedding_val]
  omega

/-- A binary vector acts by translation separately on each two-point fibre. -/
def binaryPairTranslation (r : ℕ) :
    Multiplicative (Fin r → ZMod 2) →* Equiv.Perm (Fin r × ZMod 2) where
  toFun v := Equiv.prodCongrRight fun i => Equiv.addLeft (v.toAdd i)
  map_one' := by
    apply Equiv.ext
    rintro ⟨i, b⟩
    change (i, (0 : ZMod 2) + b) = (i, b)
    simp
  map_mul' := by
    intro v w
    apply Equiv.ext
    rintro ⟨i, b⟩
    change (i, (v.toAdd i + w.toAdd i) + b) = (i, v.toAdd i + (w.toAdd i + b))
    rw [add_assoc]

@[simp] theorem binaryPairTranslation_apply (r : ℕ)
    (v : Multiplicative (Fin r → ZMod 2)) (p : Fin r × ZMod 2) :
    binaryPairTranslation r v p = (p.1, v.toAdd p.1 + p.2) := rfl

/-- Evaluation on `(i,0)` recovers coordinate `i`, so no nonzero vector acts
trivially and no two vectors induce the same permutation. -/
theorem binaryPairTranslation_injective (r : ℕ) :
    Function.Injective (binaryPairTranslation r) := by
  intro v w hvw
  apply Multiplicative.toAdd.injective
  funext i
  have h := congrArg (fun g : Equiv.Perm (Fin r × ZMod 2) => (g (i, 0)).2) hvw
  simpa using h

/-- Extend the independent pair translations to all `n` labelled points,
fixing every point outside the embedded pairs. -/
def binaryPairAction (n : ℕ) :
    Multiplicative (Fin (halfDegree n) → ZMod 2) →* Equiv.Perm (Fin n) :=
  (Equiv.Perm.viaEmbeddingHom (binaryPairEmbedding n)).comp
    (binaryPairTranslation (halfDegree n))

theorem binaryPairAction_apply (n : ℕ)
    (v : Multiplicative (Fin (halfDegree n) → ZMod 2))
    (p : Fin (halfDegree n) × ZMod 2) :
    binaryPairAction n v (binaryPairEmbedding n p) =
      binaryPairEmbedding n (p.1, v.toAdd p.1 + p.2) :=
  Equiv.Perm.viaEmbedding_apply (binaryPairTranslation (halfDegree n) v)
    (binaryPairEmbedding n) p

theorem binaryPairAction_apply_of_notMem (n : ℕ)
    (v : Multiplicative (Fin (halfDegree n) → ZMod 2)) (j : Fin n)
    (hj : j ∉ Set.range (binaryPairEmbedding n)) : binaryPairAction n v j = j :=
  Equiv.Perm.viaEmbedding_apply_of_notMem (binaryPairTranslation (halfDegree n) v)
    (binaryPairEmbedding n) j hj

/-- In odd degree the point beyond the last complete pair is fixed. The
same statement in even degree has no points satisfying its hypothesis. -/
theorem binaryPairAction_fixes_unpaired_points (n : ℕ)
    (v : Multiplicative (Fin (halfDegree n) → ZMod 2)) (j : Fin n)
    (hj : 2 * halfDegree n ≤ j.val) : binaryPairAction n v j = j := by
  apply binaryPairAction_apply_of_notMem
  rintro ⟨p, rfl⟩
  exact (not_le_of_gt (binaryPairEmbedding_val_lt n p)) hj

theorem binaryPairAction_injective (n : ℕ) : Function.Injective (binaryPairAction n) :=
  (Equiv.Perm.viaEmbeddingHom_injective (binaryPairEmbedding n)).comp
    (binaryPairTranslation_injective (halfDegree n))

/-- The actual permutation subgroup attached to an actual binary subspace. -/
def binarySubspaceSubgroup (n : ℕ)
    (U : Submodule (ZMod 2) (Fin (halfDegree n) → ZMod 2)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  U.toAddSubgroup.toSubgroup.map (binaryPairAction n)

/-- Injective transport preserves distinct subspaces as distinct subgroups;
no quotient by conjugacy or isomorphism is taken. -/
theorem binarySubspaceSubgroup_injective (n : ℕ) :
    Function.Injective (binarySubspaceSubgroup n) := by
  intro U V h
  apply Submodule.toAddSubgroup_injective
  apply AddSubgroup.toSubgroup.injective
  exact Subgroup.map_injective (binaryPairAction_injective n) h

/-- A uniform lower bound in every degree, from the single fixed system of
labelled pairs. This is much weaker than the asymptotic target T1. -/
theorem binarySubspaceCount_le_subgroupCount (n : ℕ) :
    binarySubspaceCount (halfDegree n) ≤ subgroupCount n :=
  Nat.card_le_card_of_injective (binarySubspaceSubgroup n)
    (binarySubspaceSubgroup_injective n)

/-- The same lower bound in terms of the approved finite Gaussian sum. -/
theorem binaryGaussianSum_le_subgroupCount (n : ℕ) :
    (binaryGaussianSum (halfDegree n) : ℝ) ≤ (subgroupCount n : ℝ) := by
  have hcast : (binarySubspaceCount (halfDegree n) : ℝ) =
      (binaryGaussianSum (halfDegree n) : ℝ) := by
    exact_mod_cast binarySubspaceCount_eq_gaussianSum (halfDegree n)
  rw [← hcast]
  exact_mod_cast binarySubspaceCount_le_subgroupCount n

end SymmetricSubgroupAsymptotics
