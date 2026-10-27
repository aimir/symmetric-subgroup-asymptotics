import SymmetricSubgroupAsymptotics.CFSGYE6SelectedWords

/-! Short literal conjugation certificates imply the required original-Y
commutations. The cube certificate gives the third actual derived cube.
Certificate checks are explicit finite proof data, not model bounds.
No independence, normalizer, Heisenberg or full-centre injection is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6BraidCertificateConsumers
open CFSG.Models.YGroups InvolutionBraidTrace CFSGYE6SelectedWords

private theorem conjugation_commute {G : Type*} [Group G] (w x y z : G)
    (h : w⁻¹ * x * w = y) (hc : Commute y z) : Commute x (w * z * w⁻¹) := by
  have hx : x = w * y * w⁻¹ := by rw [← h]; group
  change x * (w * z * w⁻¹) = (w * z * w⁻¹) * x
  calc
    _ = (w * y * w⁻¹) * (w * z * w⁻¹) := by rw [hx]
    _ = w * (y * z) * w⁻¹ := by group
    _ = w * (z * y) * w⁻¹ := by rw [hc.eq]
    _ = (w * z * w⁻¹) * (w * y * w⁻¹) := by group
    _ = _ := by rw [← hx]

theorem conjugation_of_identity (arms : Arms) (i j : Fin 6)
    (h : eval arms (guideW.reverse ++ [i] ++ guideW ++ [j])=1) :
    (eval arms guideW)⁻¹ * generator arms i * eval arms guideW = generator arms j := by
  have hs (k : Fin 6) : value (generator arms) [k] = generator arms k := by simp [value]
  have hh : ((eval arms guideW)⁻¹ * generator arms i * eval arms guideW) *
      generator arms j = 1 := by
    simpa only [eval,value_append,hs,
      value_reverse (generator arms) (generator_square arms) guideW,mul_assoc] using h
  have hj : (generator arms j)⁻¹ = generator arms j :=
    inv_eq_of_mul_eq_one_right (generator_square arms j)
  apply mul_inv_eq_one.mp
  rw [hj]
  exact hh

theorem theta_description (arms : Arms) : eval arms thetaWord =
    eval arms guideW * generator arms 5 * (eval arms guideW)⁻¹ := by
  have hs : value (generator arms) [5]=generator arms 5 := by simp [value]
  simp only [thetaWord,eval,value_append,hs,
    value_reverse (generator arms) (generator_square arms) guideW,mul_assoc]

theorem theta_square (arms : Arms) : eval arms thetaWord ^ 2=1 := by
  rw [theta_description]
  calc
    (eval arms guideW*generator arms 5*(eval arms guideW)⁻¹)^2 =
      eval arms guideW*(generator arms 5*generator arms 5)*(eval arms guideW)⁻¹ := by
        rw [pow_two]
        group
    _ = 1 := by rw [generator_square]; group

theorem theta_commutes_of_identity (arms : Arms) (i j : Fin 6)
    (hj : adjacent j 5=false)
    (h : eval arms (guideW.reverse ++ [i] ++ guideW ++ [j])=1) :
    Commute (generator arms i) (eval arms thetaWord) := by
  rw [theta_description]
  exact conjugation_commute _ _ _ _ (conjugation_of_identity arms i j h)
    (generator_commute arms j 5 hj)

theorem conjugation_of_trace (arms : Arms) (i j : Fin 6)
    (steps : List (Step (Fin 6)))
    (hcheck : check adjacent (guideW.reverse ++ [i] ++ guideW ++ [j]) steps = true) :
    (eval arms guideW)⁻¹ * generator arms i * eval arms guideW = generator arms j := by
  have h := checked_trace_identity arms _ steps hcheck
  have hs (k : Fin 6) : value (generator arms) [k] = generator arms k := by simp [value]
  have hh : ((eval arms guideW)⁻¹ * generator arms i * eval arms guideW) *
      generator arms j = 1 := by
    simpa only [eval, value_append, hs,
      value_reverse (generator arms) (generator_square arms) guideW, mul_assoc] using h
  have hj : (generator arms j)⁻¹ = generator arms j :=
    inv_eq_of_mul_eq_one_right (generator_square arms j)
  apply mul_inv_eq_one.mp
  rw [hj]
  exact hh

theorem theta_commutes_of_trace (arms : Arms) (i j : Fin 6)
    (hj : adjacent j 5 = false)
    (steps : List (Step (Fin 6)))
    (hcheck : check adjacent (guideW.reverse ++ [i] ++ guideW ++ [j]) steps = true) :
    Commute (generator arms i) (eval arms thetaWord) := by
  have hs : value (generator arms) [5] = generator arms 5 := by simp [value]
  have ht : eval arms thetaWord =
      eval arms guideW * generator arms 5 * (eval arms guideW)⁻¹ := by
    simp only [thetaWord, eval, value_append, hs,
      value_reverse (generator arms) (generator_square arms) guideW,mul_assoc]
  rw [ht]
  exact conjugation_commute _ _ _ _ (conjugation_of_trace arms i j steps hcheck)
    (generator_commute arms j 5 hj)

theorem third_cube_of_trace (arms : Arms) (steps : List (Step (Fin 6)))
    (hcheck : check adjacent (wordC ++ wordC ++ wordC) steps = true) :
    derivedC arms ^ 3 = 1 := by
  have h := checked_trace_identity arms _ steps hcheck
  apply Subtype.ext
  change eval arms wordC ^ 3 = 1
  simpa only [eval, value_append, pow_succ, pow_zero, mul_one, mul_assoc] using h

theorem derivedA_commutes_derivedB (arms : Arms) : Commute (derivedA arms) (derivedB arms) := by
  have h13 : Commute (generator arms 1) (generator arms 3) := generator_commute arms 1 3 rfl
  have h14 : Commute (generator arms 1) (generator arms 4) := generator_commute arms 1 4 rfl
  have h23 : Commute (generator arms 2) (generator arms 3) := generator_commute arms 2 3 rfl
  have h24 : Commute (generator arms 2) (generator arms 4) := generator_commute arms 2 4 rfl
  have h := ((h13.mul_left h23).mul_right (h14.mul_left h24)).eq
  change derivedA arms * derivedB arms = derivedB arms * derivedA arms
  apply Subtype.ext
  change eval arms wordA * eval arms wordB = eval arms wordB * eval arms wordA
  simpa only [eval, wordA, wordB, value, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one] using h

end SymmetricSubgroupAsymptotics.CFSGYE6BraidCertificateConsumers
