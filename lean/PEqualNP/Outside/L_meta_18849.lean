import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18849

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def x1Set : Finset (Fin 13) := {0, 1, 3, 9}

private def x2List : List (Fin 26) :=
  [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldW_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [stepW]
    omega

private theorem foldW_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepW w g) (by simp [stepW]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private def remapW (u : ℕ) : ℕ :=
  if u < 21 then (x2List.getD u 0).val else 26 + (u - 21)

private def remapGate (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map remapW⟩

private theorem remapW_lt_26 (u : ℕ) (hu : u < 21) : remapW u < 26 := by
  simp only [remapW, hu, ↓reduceIte]
  exact (x2List.getD u 0).isLt

private theorem remapW_lt_base (u s : ℕ) (hu : u < 21 + s) : remapW u < 26 + s := by
  by_cases h : u < 21
  · have := remapW_lt_26 u h; omega
  · simp only [remapW, h, ↓reduceIte]; omega

private theorem fold_remap (gs : List Gate) :
    ∀ (w4 w8 : List Bool),
      w4.length ≥ 21 →
      w8.length = 26 + (w4.length - 21) →
      (∀ u < w4.length, w8.getD (remapW u) false = w4.getD u false) →
      (∀ u < (gs.foldl stepW w4).length,
        ((gs.map remapGate).foldl stepW w8).getD (remapW u) false =
          (gs.foldl stepW w4).getD u false) := by
  induction gs with
  | nil =>
    intro w4 w8 _ _ hEq u hu
    exact hEq u hu
  | cons g gs ih =>
    intro w4 w8 h4len h8len hEq
    simp only [List.map_cons, List.foldl_cons]
    have hval : (remapGate g).op.eval ((remapGate g).inputs.map fun i => w8.getD i false) =
        g.op.eval (g.inputs.map fun i => w4.getD i false) := by
      simp only [remapGate, List.map_map]
      congr 1
      refine List.map_congr_left fun u _ => ?_
      simp only [Function.comp_apply]
      by_cases hu : u < w4.length
      · exact hEq u hu
      · have hge4 : w4.length ≤ u := by omega
        have hnot21 : ¬ u < 21 := by omega
        have hge8 : w8.length ≤ remapW u := by
          simp only [remapW, hnot21, ↓reduceIte]; omega
        rw [List.getD_eq_default _ _ hge8, List.getD_eq_default _ _ hge4]
    refine ih (stepW w4 g) (stepW w8 (remapGate g)) (by simp [stepW]; omega)
      (by simp [stepW]; omega) ?_
    intro u hu
    simp only [stepW, List.length_append, List.length_singleton] at hu
    by_cases hlt : u < w4.length
    · have hrlt : remapW u < w8.length := by
        by_cases h21 : u < 21
        · have := remapW_lt_26 u h21; omega
        · simp only [remapW, h21, ↓reduceIte]; omega
      simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        List.getElem?_append_left hrlt]
      exact hEq u hlt
    · have hueq : u = w4.length := by omega
      subst hueq
      have hnot21 : ¬ w4.length < 21 := by omega
      have hreq : remapW w4.length = w8.length := by
        simp only [remapW, hnot21, ↓reduceIte]; omega
      simp only [stepW, List.getD_eq_getElem?_getD, hreq]
      rw [List.getElem?_append_right le_rfl, Nat.sub_self,
          List.getElem?_append_right le_rfl, Nat.sub_self]
      simpa [List.getD_eq_getElem?_getD] using hval

private def extraGates (B : ℕ) : List Gate :=
  [ ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.or, [16, 22]⟩,
    ⟨GateOp.or, [B, B + 1]⟩,
    ⟨GateOp.and, [0, B + 2]⟩,
    ⟨GateOp.or, [25, 13]⟩,
    ⟨GateOp.or, [15, 21]⟩,
    ⟨GateOp.or, [B + 4, B + 5]⟩,
    ⟨GateOp.and, [1, B + 6]⟩,
    ⟨GateOp.or, [23, 24]⟩,
    ⟨GateOp.or, [13, 19]⟩,
    ⟨GateOp.or, [B + 8, B + 9]⟩,
    ⟨GateOp.and, [3, B + 10]⟩,
    ⟨GateOp.or, [17, 18]⟩,
    ⟨GateOp.or, [20, 13]⟩,
    ⟨GateOp.or, [B + 12, B + 13]⟩,
    ⟨GateOp.and, [9, B + 14]⟩,
    ⟨GateOp.or, [B + 3, B + 7]⟩,
    ⟨GateOp.or, [B + 11, B + 15]⟩,
    ⟨GateOp.or, [B + 16, B + 17]⟩ ]

private theorem extraGates_len (B : ℕ) : (extraGates B).length = 19 := rfl

private theorem extraGates_mono (B : ℕ) : ∀ g ∈ extraGates B,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [extraGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem extraGates_eval_clean (B : ℕ) (w : List Bool) (x11 : Fin 26 → Bool)
    (hwlen : w.length = B) (hB : 26 ≤ B)
    (hwin : ∀ i : Fin 26, w.getD i.val false = x11 i) :
    ((extraGates B).foldl stepW w).getD (B + 18) false =
      (((x11 0 && ((x11 13 || x11 14) || (x11 16 || x11 22))) ||
        (x11 1 && ((x11 25 || x11 13) || (x11 15 || x11 21)))) ||
       ((x11 3 && ((x11 23 || x11 24) || (x11 13 || x11 19))) ||
        (x11 9 && ((x11 17 || x11 18) || (x11 20 || x11 13))))) := by
  have hi : ∀ (k : ℕ) (hk : k < 26), w.getD k false = x11 ⟨k, hk⟩ := fun k hk => hwin ⟨k, hk⟩
  let v0 := x11 13 || x11 14
  let v1 := x11 16 || x11 22
  let v2 := v0 || v1
  let v3 := x11 0 && v2
  let v4 := x11 25 || x11 13
  let v5 := x11 15 || x11 21
  let v6 := v4 || v5
  let v7 := x11 1 && v6
  let v8 := x11 23 || x11 24
  let v9 := x11 13 || x11 19
  let v10 := v8 || v9
  let v11 := x11 3 && v10
  let v12 := x11 17 || x11 18
  let v13 := x11 20 || x11 13
  let v14 := v12 || v13
  let v15 := x11 9 && v14
  let v16 := v3 || v7
  let v17 := v11 || v15
  let v18 := v16 || v17
  have step_or : ∀ (l : List Bool) (a b : ℕ),
      stepW l ⟨GateOp.or, [a, b]⟩ = l ++ [l.getD a false || l.getD b false] := by
    intro l a b; simp [stepW, GateOp.eval]
  have step_and : ∀ (l : List Bool) (a b : ℕ),
      stepW l ⟨GateOp.and, [a, b]⟩ = l ++ [l.getD a false && l.getD b false] := by
    intro l a b; simp [stepW, GateOp.eval]
  have hpre : ∀ (sfx : List Bool) (k : ℕ) (hk : k < 26), (w ++ sfx).getD k false = x11 ⟨k, hk⟩ := by
    intro sfx k hk
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hi k hk
  have hsfx : ∀ (sfx : List Bool) (j : ℕ) (hj : j < sfx.length),
      (w ++ sfx).getD (B + j) false = sfx[j] := by
    intro sfx j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    rw [hwlen, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj]
    rfl
  have s0 : stepW w ⟨GateOp.or, [13, 14]⟩ = w ++ [v0] := by
    rw [step_or, hi 13 (by omega), hi 14 (by omega)]; rfl
  have s1 : stepW (w ++ [v0]) ⟨GateOp.or, [16, 22]⟩ = w ++ [v0, v1] := by
    rw [step_or, hpre _ 16 (by omega), hpre _ 22 (by omega), List.append_assoc]; rfl
  have s2 : stepW (w ++ [v0, v1]) ⟨GateOp.or, [B, B + 1]⟩ = w ++ [v0, v1, v2] := by
    rw [step_or, show B = B + 0 by omega, hsfx _ 0 (by simp), hsfx _ 1 (by simp), List.append_assoc]; rfl
  have s3 : stepW (w ++ [v0, v1, v2]) ⟨GateOp.and, [0, B + 2]⟩ = w ++ [v0, v1, v2, v3] := by
    rw [step_and, hpre _ 0 (by omega), hsfx _ 2 (by simp), List.append_assoc]; rfl
  have s4 : stepW (w ++ [v0, v1, v2, v3]) ⟨GateOp.or, [25, 13]⟩ = w ++ [v0, v1, v2, v3, v4] := by
    rw [step_or, hpre _ 25 (by omega), hpre _ 13 (by omega), List.append_assoc]; rfl
  have s5 : stepW (w ++ [v0, v1, v2, v3, v4]) ⟨GateOp.or, [15, 21]⟩ = w ++ [v0, v1, v2, v3, v4, v5] := by
    rw [step_or, hpre _ 15 (by omega), hpre _ 21 (by omega), List.append_assoc]; rfl
  have s6 : stepW (w ++ [v0, v1, v2, v3, v4, v5]) ⟨GateOp.or, [B + 4, B + 5]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6] := by
    rw [step_or, hsfx _ 4 (by simp), hsfx _ 5 (by simp), List.append_assoc]; rfl
  have s7 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6]) ⟨GateOp.and, [1, B + 6]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7] := by
    rw [step_and, hpre _ 1 (by omega), hsfx _ 6 (by simp), List.append_assoc]; rfl
  have s8 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7]) ⟨GateOp.or, [23, 24]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8] := by
    rw [step_or, hpre _ 23 (by omega), hpre _ 24 (by omega), List.append_assoc]; rfl
  have s9 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8]) ⟨GateOp.or, [13, 19]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] := by
    rw [step_or, hpre _ 13 (by omega), hpre _ 19 (by omega), List.append_assoc]; rfl
  have s10 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]) ⟨GateOp.or, [B + 8, B + 9]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] := by
    rw [step_or, hsfx _ 8 (by simp), hsfx _ 9 (by simp), List.append_assoc]; rfl
  have s11 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]) ⟨GateOp.and, [3, B + 10]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] := by
    rw [step_and, hpre _ 3 (by omega), hsfx _ 10 (by simp), List.append_assoc]; rfl
  have s12 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]) ⟨GateOp.or, [17, 18]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] := by
    rw [step_or, hpre _ 17 (by omega), hpre _ 18 (by omega), List.append_assoc]; rfl
  have s13 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]) ⟨GateOp.or, [20, 13]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] := by
    rw [step_or, hpre _ 20 (by omega), hpre _ 13 (by omega), List.append_assoc]; rfl
  have s14 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]) ⟨GateOp.or, [B + 12, B + 13]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] := by
    rw [step_or, hsfx _ 12 (by simp), hsfx _ 13 (by simp), List.append_assoc]; rfl
  have s15 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]) ⟨GateOp.and, [9, B + 14]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := by
    rw [step_and, hpre _ 9 (by omega), hsfx _ 14 (by simp), List.append_assoc]; rfl
  have s16 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]) ⟨GateOp.or, [B + 3, B + 7]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16] := by
    rw [step_or, hsfx _ 3 (by simp), hsfx _ 7 (by simp), List.append_assoc]; rfl
  have s17 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]) ⟨GateOp.or, [B + 11, B + 15]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17] := by
    rw [step_or, hsfx _ 11 (by simp), hsfx _ 15 (by simp), List.append_assoc]; rfl
  have s18 : stepW (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]) ⟨GateOp.or, [B + 16, B + 17]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18] := by
    rw [step_or, hsfx _ 16 (by simp), hsfx _ 17 (by simp), List.append_assoc]; rfl
  have hvals : (extraGates B).foldl stepW w =
      w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18] := by
    simp only [extraGates, List.foldl_cons, List.foldl_nil, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9,
      s10, s11, s12, s13, s14, s15, s16, s17, s18]
  rw [hvals]
  exact hsfx [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18] 18 (by simp)

private theorem rest_iff (x11 : Fin 26 → Bool) :
    (((x11 0 && ((x11 13 || x11 14) || (x11 16 || x11 22))) ||
      (x11 1 && ((x11 25 || x11 13) || (x11 15 || x11 21)))) ||
     ((x11 3 && ((x11 23 || x11 24) || (x11 13 || x11 19))) ||
      (x11 9 && ((x11 17 || x11 18) || (x11 20 || x11 13))))) =
    decide (∃ p ∈ x1Set, ∃ l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
      x11 (Fin.castAdd 13 p) = true ∧ x11 (Fin.natAdd 13 l) = true) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [Bool.or_eq_true, Bool.and_eq_true, x1Set, Finset.mem_insert, Finset.mem_singleton]
  have hdec0 : ∀ l : Fin 13, (0 + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
      l = 0 ∨ l = 1 ∨ l = 3 ∨ l = 9 := by decide
  have hdec1 : ∀ l : Fin 13, (1 + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
      l = 12 ∨ l = 0 ∨ l = 2 ∨ l = 8 := by decide
  have hdec3 : ∀ l : Fin 13, (3 + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
      l = 10 ∨ l = 11 ∨ l = 0 ∨ l = 6 := by decide
  have hdec9 : ∀ l : Fin 13, (9 + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
      l = 4 ∨ l = 5 ∨ l = 7 ∨ l = 0 := by decide
  constructor
  · rintro ((⟨hp, (hl | hl) | (hl | hl)⟩ | ⟨hp, (hl | hl) | (hl | hl)⟩) |
            (⟨hp, (hl | hl) | (hl | hl)⟩ | ⟨hp, (hl | hl) | (hl | hl)⟩))
    · exact ⟨0, Or.inl rfl, 0, by decide, hp, hl⟩
    · exact ⟨0, Or.inl rfl, 1, by decide, hp, hl⟩
    · exact ⟨0, Or.inl rfl, 3, by decide, hp, hl⟩
    · exact ⟨0, Or.inl rfl, 9, by decide, hp, hl⟩
    · exact ⟨1, Or.inr (Or.inl rfl), 12, by decide, hp, hl⟩
    · exact ⟨1, Or.inr (Or.inl rfl), 0, by decide, hp, hl⟩
    · exact ⟨1, Or.inr (Or.inl rfl), 2, by decide, hp, hl⟩
    · exact ⟨1, Or.inr (Or.inl rfl), 8, by decide, hp, hl⟩
    · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)), 10, by decide, hp, hl⟩
    · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)), 11, by decide, hp, hl⟩
    · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)), 0, by decide, hp, hl⟩
    · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)), 6, by decide, hp, hl⟩
    · exact ⟨9, Or.inr (Or.inr (Or.inr rfl)), 4, by decide, hp, hl⟩
    · exact ⟨9, Or.inr (Or.inr (Or.inr rfl)), 5, by decide, hp, hl⟩
    · exact ⟨9, Or.inr (Or.inr (Or.inr rfl)), 7, by decide, hp, hl⟩
    · exact ⟨9, Or.inr (Or.inr (Or.inr rfl)), 0, by decide, hp, hl⟩
  · rintro ⟨p, hp, l, hinc, hxp, hxl⟩
    rcases hp with rfl | rfl | rfl | rfl
    · left; left; refine ⟨hxp, ?_⟩
      rcases (hdec0 l).mp hinc with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxl)
      · exact Or.inl (Or.inr hxl)
      · exact Or.inr (Or.inl hxl)
      · exact Or.inr (Or.inr hxl)
    · left; right; refine ⟨hxp, ?_⟩
      rcases (hdec1 l).mp hinc with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxl)
      · exact Or.inl (Or.inr hxl)
      · exact Or.inr (Or.inl hxl)
      · exact Or.inr (Or.inr hxl)
    · right; left; refine ⟨hxp, ?_⟩
      rcases (hdec3 l).mp hinc with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxl)
      · exact Or.inl (Or.inr hxl)
      · exact Or.inr (Or.inl hxl)
      · exact Or.inr (Or.inr hxl)
    · right; right; refine ⟨hxp, ?_⟩
      rcases (hdec9 l).mp hinc with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxl)
      · exact Or.inl (Or.inr hxl)
      · exact Or.inr (Or.inl hxl)
      · exact Or.inr (Or.inr hxl)

theorem main_proof :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
     have x2 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];
     let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.size ≤ (43 : ℕ) → x4.output < (21 : ℕ) + x4.size → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x4.size + (19 : ℕ) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x9 < x10 ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), ((x8.wires (List.ofFn x11)).getD x9 Bool.false || (x8.wires (List.ofFn x11)).getD x10 Bool.false) = (x4.eval (List.map x11 x2) || Decidable.decide (∃ x12 ∈ x1, ∃ (x13 : Fin (13 : ℕ)), x3 x12 x13 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true))) := by
  dsimp only
  intro C hMono _ hOutLt
  let B : ℕ := 26 + C.size
  let D : Circuit := ⟨C.gates.map remapGate ++ extraGates B, B + 18⟩
  have hDmono : Monotone2 D := by
    intro g hg
    rcases List.mem_append.mp hg with h1 | h2
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
      obtain ⟨hop, hlen⟩ := hMono g0 hg0
      exact ⟨hop, by simp [remapGate, hlen]⟩
    · exact extraGates_mono B g h2
  have hDsize : D.size ≤ C.size + 19 := by
    change (C.gates.map remapGate ++ extraGates B).length ≤ C.gates.length + 19
    simp [extraGates_len]
  let x9 : ℕ := remapW C.output
  let x10 : ℕ := B + 18
  have hx9lt : x9 < B := remapW_lt_base C.output C.size hOutLt
  refine ⟨D, hDmono, hDsize, x9, x10, by omega, ?_⟩
  intro x11
  let w4 := C.gates.foldl stepW (List.map x11 x2List)
  let w8pre := (C.gates.map remapGate).foldl stepW (List.ofFn x11)
  have hw8pre_len : w8pre.length = B := by
    simp [w8pre, B, foldW_len, Circuit.size]
  have hw8pre_in : ∀ i : Fin 26, w8pre.getD i.val false = x11 i := by
    intro i
    simp only [w8pre]
    rw [foldW_getD _ _ i.val (by simp)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [i.isLt]
  have hw4_eq : w8pre.getD x9 false = C.eval (List.map x11 x2List) := by
    have hinit : ∀ u < (List.map x11 x2List).length,
        (List.ofFn x11).getD (remapW u) false = (List.map x11 x2List).getD u false := by
      intro u hu
      have hu21 : u < 21 := by simpa [x2List] using hu
      simp only [remapW, hu21, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [(x2List.getD u 0).isLt, ↓reduceDIte, Option.getD_some, Fin.eta]
      rw [List.getD_eq_getElem _ _ hu, List.getElem_map]
      congr 1
      rw [List.getD_eq_getElem _ _ (by simpa [x2List] using hu21)]
    have hres := fold_remap C.gates (List.map x11 x2List) (List.ofFn x11)
      (by simp [x2List]) (by simp [x2List]) hinit C.output
      (by rw [foldW_len]; simpa [x2List, Circuit.size] using hOutLt)
    exact hres
  have h1 : (D.wires (List.ofFn x11)).getD x9 false = C.eval (List.map x11 x2List) := by
    change ((C.gates.map remapGate ++ extraGates B).foldl stepW (List.ofFn x11)).getD x9 false = _
    rw [List.foldl_append]
    rw [foldW_getD (extraGates B) w8pre x9 (by rw [hw8pre_len]; exact hx9lt)]
    exact hw4_eq
  have h2 : (D.wires (List.ofFn x11)).getD x10 false =
      decide (∃ p ∈ x1Set, ∃ l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        x11 (Fin.castAdd 13 p) = true ∧ x11 (Fin.natAdd 13 l) = true) := by
    change ((C.gates.map remapGate ++ extraGates B).foldl stepW (List.ofFn x11)).getD (B + 18) false = _
    rw [List.foldl_append]
    rw [extraGates_eval_clean B w8pre x11 hw8pre_len (by omega) hw8pre_in]
    exact rest_iff x11
  rw [h1, h2]
  rfl

end PEqualNP.Outside.L_meta_18849

theorem PEqualNP.Outside.L_meta_18849 : (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))]; let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.size ≤ (43 : ℕ) → x4.output < (21 : ℕ) + x4.size → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x4.size + (19 : ℕ) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x9 < x10 ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), ((x8.wires (List.ofFn x11)).getD x9 Bool.false || (x8.wires (List.ofFn x11)).getD x10 Bool.false) = (x4.eval (List.map x11 x2) || Decidable.decide (∃ x12 ∈ x1, ∃ (x13 : Fin (13 : ℕ)), x3 x12 x13 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true))) :=
  PEqualNP.Outside.L_meta_18849.main_proof
