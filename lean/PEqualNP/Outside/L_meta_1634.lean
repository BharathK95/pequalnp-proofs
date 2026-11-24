import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1634

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma getD_append_left (xs ys : List Bool) (w : ℕ) (hw : w < xs.length) :
    (xs ++ ys).getD w false = xs.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

lemma getD_append_singleton_eq (xs : List Bool) (b : Bool) :
    (xs ++ [b]).getD xs.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge_length (xs : List Bool) (w : ℕ) (hw : xs.length ≤ w) :
    xs.getD w false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hw]

lemma run_mono (gs : List Gate)
    (hbasis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ k, x.getD k false = true → y.getD k false = true) :
    ∀ k, (run gs x).getD k false = true → (run gs y).getD k false = true := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hbasis g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hmem => hbasis g' (by simp [hmem])
    have hstep :
        g.op.eval (g.inputs.map fun i => x.getD i false) = true →
        g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
      rcases hg with hand | hor
      · rw [hand]
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂]
        intro hall a ha
        exact hxy a (hall a ha)
      · rw [hor]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨_, ⟨a, ha, rfl⟩, hxa⟩
        exact ⟨y.getD a false, ⟨a, ha, rfl⟩, hxy a hxa⟩
    rw [run_cons, run_cons]
    apply ih hgs
    · simp [hlen]
    · intro k hk
      by_cases hlt : k < x.length
      · rw [getD_append_left y _ k (by omega)]
        rw [getD_append_left x _ k hlt] at hk
        exact hxy k hk
      · by_cases heq : k = x.length
        · subst heq
          rw [hlen]
          rw [getD_append_singleton_eq] at hk ⊢
          exact hstep hk
        · have hge : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).length ≤ k := by
            simp; omega
          rw [getD_ge_length _ k hge] at hk
          exact Bool.noConfusion hk

lemma one_dir {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool)
    (gates : List Gate)
    (hbasis : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (ev : ℕ → (Fin N → Bool) → Bool)
    (hev : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = Circuit.eval ⟨gates, w⟩ (List.ofFn x))
    (w : ℕ) (t u : Fin N)
    (hinter : (L t ∩ L u).card = 1)
    (hfu : ev w (fun v : Fin N => decide (v ∉ L u)) = false)
    (hcard : 2 ≤ ((L t).filter (fun p => ev w (T t p) = true)).card) :
    ∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true := by
  let F : Finset (Fin N) := (L t).filter (fun p => ev w (T t p) = true)
  have hex_p : ∃ p ∈ F, p ∉ L u := by
    by_contra hnone
    push Not at hnone
    have hsub : F ⊆ L t ∩ L u := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, hnone p hp⟩
    have hle : F.card ≤ (L t ∩ L u).card := Finset.card_le_card hsub
    rw [hinter] at hle
    have hcard' : 2 ≤ F.card := hcard
    omega
  rcases hex_p with ⟨p, hpF, hpLu⟩
  have hpLt : p ∈ L t := (Finset.mem_filter.mp hpF).1
  have hp_true : ev w (T t p) = true := (Finset.mem_filter.mp hpF).2
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hpLt, hpLu⟩, ?_⟩
  by_contra hno_v
  push Not at hno_v
  have hle_pt : ∀ k, (List.ofFn (T t p)).getD k false = true →
      (List.ofFn (fun v : Fin N => decide (v ∉ L u))).getD k false = true := by
    intro k hk
    by_cases hkN : k < N
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hkN, ↓reduceDIte,
        Option.getD_some, decide_eq_true_eq] at hk ⊢
      intro hmem
      exact hno_v ⟨k, hkN⟩ hmem hk
    · have hge : (List.ofFn (T t p)).length ≤ k := by simp; omega
      rw [getD_ge_length _ k hge] at hk
      exact Bool.noConfusion hk
  have hmon := run_mono gates (fun gt hgt => (hbasis gt hgt).1)
    (List.ofFn (T t p)) (List.ofFn (fun v : Fin N => decide (v ∉ L u)))
    (by simp) hle_pt w (by simpa [hev, Circuit.eval, Circuit.wires, run] using hp_true)
  have hfu' : (run gates (List.ofFn (fun v : Fin N => decide (v ∉ L u)))).getD w false = false := by
    simpa [hev, Circuit.eval, Circuit.wires, run] using hfu
  rw [hfu'] at hmon
  exact Bool.noConfusion hmon

end PEqualNP.Outside.L_meta_1634

theorem PEqualNP.Outside.L_meta_1634 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ (w : ℕ) (t u : Fin N), t ≠ u → ev w (fun v : Fin N => decide (v ∉ L t)) = false → ev w (fun v : Fin N => decide (v ∉ L u)) = false →
      2 ≤ ((L t).filter (fun p => ev w (T t p) = true)).card → 2 ≤ ((L u).filter (fun p => ev w (T u p) = true)).card →
      (∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) := by
  intro q N L i0 p0 p1 _ _ _ hinter _ _ _ _ T _ gates hbasis _ _ ev hev w t u htu hft hfu hct hcu
  exact ⟨PEqualNP.Outside.L_meta_1634.one_dir L T gates hbasis ev hev w t u (hinter t u htu) hfu hct,
    PEqualNP.Outside.L_meta_1634.one_dir L T gates hbasis ev hev w u t (hinter u t (Ne.symm htu)) hft hcu⟩
