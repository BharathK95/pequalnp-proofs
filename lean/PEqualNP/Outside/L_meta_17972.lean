import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17972

open PEqualNP.CircuitLowerBounds

def stepList (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (bs1 bs2 : List Bool) (hlen : bs1.length = bs2.length)
    (hle : ∀ i, bs1.getD i false = true → bs2.getD i false = true) :
    op.eval bs1 = true → op.eval bs2 = true := by
  have hmem : ∀ i, i < bs1.length → bs1[i]? = some true → bs2[i]? = some true := by
    intro i _ hi
    have h1 : bs1.getD i false = true := by
      simp [List.getD_eq_getElem?_getD, hi]
    have h2 := hle i h1
    simp only [List.getD_eq_getElem?_getD] at h2
    cases h : bs2[i]? with
    | none => simp [h] at h2
    | some b =>
      simp [h] at h2
      simp [h2]
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rw [List.mem_iff_getElem?] at hb
    obtain ⟨i, hi⟩ := hb
    have hi_lt : i < bs1.length := by
      have : i < bs2.length := by
        cases hlt : decide (i < bs2.length) with
        | true => exact of_decide_eq_true hlt
        | false =>
          have hge : bs2.length ≤ i := by
            have := of_decide_eq_false hlt; omega
          rw [List.getElem?_eq_none hge] at hi
          cases hi
      omega
    have h1i : bs1[i]? = some bs1[i] := List.getElem?_eq_getElem hi_lt
    have h1t : bs1[i] = true := h1 bs1[i] (List.getElem_mem hi_lt)
    rw [h1t] at h1i
    have h2i := hmem i hi_lt h1i
    rw [h2i] at hi
    exact Option.some.inj hi.symm
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    rw [List.mem_iff_getElem?] at hb
    obtain ⟨i, hi⟩ := hb
    have hi_lt : i < bs1.length := by
      cases hlt : decide (i < bs1.length) with
      | true => exact of_decide_eq_true hlt
      | false =>
        have hge : bs1.length ≤ i := by
          have := of_decide_eq_false hlt; omega
        rw [List.getElem?_eq_none hge] at hi
        cases hi
    have h2i := hmem i hi_lt hi
    exact ⟨true, List.mem_iff_getElem?.mpr ⟨i, h2i⟩, rfl⟩

theorem foldl_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    ∀ i, (gs.foldl stepList w1).getD i false = true →
      (gs.foldl stepList w2).getD i false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    · simp [stepList, hlen]
    · intro i hi
      simp only [stepList, List.getD_eq_getElem?_getD] at hi ⊢
      by_cases hlt : i < w1.length
      · have hlt2 : i < w2.length := by omega
        rw [List.getElem?_append_left hlt] at hi
        rw [List.getElem?_append_left hlt2]
        have h1 : w1.getD i false = true := by simpa [List.getD_eq_getElem?_getD] using hi
        have h2 := hle i h1
        simpa [List.getD_eq_getElem?_getD] using h2
      · by_cases heq : i = w1.length
        · subst heq
          rw [List.getElem?_append_right (le_refl _)] at hi
          rw [hlen, List.getElem?_append_right (le_refl _)]
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
          apply gateOp_mono g.op (hgs g (by simp))
            (g.inputs.map fun idx => w1.getD idx false)
            (g.inputs.map fun idx => w2.getD idx false)
          · simp
          · intro j hj
            simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hj ⊢
            cases hidx : g.inputs[j]? with
            | none => simp [hidx] at hj
            | some idx =>
              simp only [hidx, Option.map_some, Option.getD_some] at hj ⊢
              exact hle idx (by simpa [List.getD_eq_getElem?_getD] using hj)
          · simpa [List.getD_eq_getElem?_getD] using hi
        · rw [List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi

theorem main_proof :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ x y : List Bool, x.length = y.length →
        (∀ i : ℕ, x.getD i false = true → y.getD i false = true) →
        C.eval x = true → C.eval y = true := by
  intro C hgs x y hlen hle hx
  exact foldl_mono C.gates hgs x y hlen hle C.output hx

end PEqualNP.Outside.L_meta_17972

theorem PEqualNP.Outside.L_meta_17972 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.getD x6 Bool.false = Bool.true → x4.getD x6 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true) := by
  exact PEqualNP.Outside.L_meta_17972.main_proof
