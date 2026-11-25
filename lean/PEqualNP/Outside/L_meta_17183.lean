import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17183

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents

def stepList (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireVal (C : Circuit) (xs : List Bool) (w : ℕ) : Bool :=
  (C.wires xs).getD w false

theorem length_foldl_stepList (gs : List Gate) (xs : List Bool) :
    (gs.foldl stepList xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepList, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_foldl_stepList_lt (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (gs.foldl stepList xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : w < (stepList xs g).length := by
      simp only [stepList, List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih (stepList xs g) hlt]
    simp only [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

theorem wireVal_lt (C : Circuit) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    wireVal C xs w = xs.getD w false :=
  getD_foldl_stepList_lt C.gates xs w hw

theorem wireVal_ge (C : Circuit) (xs : List Bool) (w : ℕ) (hw : xs.length + C.gates.length ≤ w) :
    wireVal C xs w = false := by
  change (C.gates.foldl stepList xs).getD w false = false
  have hlen : (C.gates.foldl stepList xs).length = xs.length + C.gates.length :=
    length_foldl_stepList C.gates xs
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

def effInputs (M : ℕ) (g : Gate) (j : ℕ) : List ℕ :=
  match g.op with
  | .not => (g.inputs.take 1).filter (fun w => decide (w < M + j))
  | _ => g.inputs.filter (fun w => decide (w < M + j))

theorem effInputs_len_le (M : ℕ) (g : Gate) (j : ℕ) (hfin : g.inputs.length ≤ 2) :
    (effInputs M g j).length ≤ 2 := by
  unfold effInputs
  cases g.op <;> simp only []
  all_goals
    calc
      _ ≤ _ := List.length_filter_le _ _
      _ ≤ 2 := by
        first
        | exact hfin
        | (have := List.length_take_le 1 g.inputs; omega)

theorem effInputs_not_len_le (M : ℕ) (g : Gate) (j : ℕ) (hnot : g.op = .not) :
    (effInputs M g j).length ≤ 1 := by
  simp only [effInputs, hnot]
  calc
    ((g.inputs.take 1).filter (fun w => decide (w < M + j))).length ≤ (g.inputs.take 1).length :=
      List.length_filter_le _ _
    _ ≤ 1 := List.length_take_le 1 g.inputs

theorem effInputs_lt (M : ℕ) (g : Gate) (j w : ℕ) (hw : w ∈ effInputs M g j) : w < M + j := by
  unfold effInputs at hw
  cases h : g.op <;> simp only [h, List.mem_filter, decide_eq_true_eq] at hw <;> exact hw.2

theorem wireVal_gate_raw (C : Circuit) (xs : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    wireVal C xs (xs.length + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < xs.length + j then wireVal C xs i else false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate]
  let pre := (C.gates.take j).foldl stepList xs
  have hpre_len : pre.length = xs.length + j := by
    simp [pre, length_foldl_stepList, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hw : C.wires xs = (C.gates.drop (j + 1)).foldl stepList (stepList pre C.gates[j]) := by
    change C.gates.foldl stepList xs = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlt_step : xs.length + j < (stepList pre C.gates[j]).length := by
    simp only [stepList, List.length_append, List.length_cons, List.length_nil, hpre_len]; omega
  have hval : wireVal C xs (xs.length + j) = (stepList pre C.gates[j]).getD (xs.length + j) false := by
    unfold wireVal; rw [hw]; exact getD_foldl_stepList_lt _ _ _ hlt_step
  rw [hval]
  have hlast : (stepList pre C.gates[j]).getD (xs.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => pre.getD i false) := by
    simp only [stepList, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), hpre_len, Nat.sub_self]
    simp
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < xs.length + j
  · simp only [hi, ite_true]
    have hi_lt : i < pre.length := by omega
    have hi_step : i < (stepList pre C.gates[j]).length := by
      simp only [stepList, List.length_append, List.length_cons, List.length_nil]; omega
    unfold wireVal
    rw [hw, getD_foldl_stepList_lt _ _ _ hi_step]
    simp only [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_left hi_lt]
  · simp only [hi, ite_false]
    have hi_ge : pre.length ≤ i := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi_ge]; rfl

theorem wireVal_gate_eq_of_eff (C : Circuit) (xs ys : List Bool) (M j : ℕ)
    (hx : xs.length = M) (hy : ys.length = M) (hj : j < C.gates.length)
    (hag : ∀ w ∈ effInputs M (gateAt C j) j, wireVal C xs w = wireVal C ys w) :
    wireVal C xs (M + j) = wireVal C ys (M + j) := by
  have hx_eq : M + j = xs.length + j := by omega
  have hy_eq : M + j = ys.length + j := by omega
  conv_lhs => rw [hx_eq]
  conv_rhs => rw [hy_eq]
  rw [wireVal_gate_raw C xs j hj, wireVal_gate_raw C ys j hj]
  cases hop : (gateAt C j).op
  · congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hlt : i < M + j
    · have hmem : i ∈ effInputs M (gateAt C j) j := by simp [effInputs, hop, hi, hlt]
      simp [hx, hy, hlt, hag i hmem]
    · simp [hx, hy, hlt]
  · congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hlt : i < M + j
    · have hmem : i ∈ effInputs M (gateAt C j) j := by simp [effInputs, hop, hi, hlt]
      simp [hx, hy, hlt, hag i hmem]
    · simp [hx, hy, hlt]
  · simp only [GateOp.eval]
    cases hins : (gateAt C j).inputs with
    | nil => simp
    | cons a t =>
      simp only [List.map_cons, List.headD_cons]
      by_cases hlt : a < M + j
      · have hmem : a ∈ effInputs M (gateAt C j) j := by simp [effInputs, hop, hins, hlt]
        simp [hx, hy, hlt, hag a hmem]
      · simp [hx, hy, hlt]
  · congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hlt : i < M + j
    · have hmem : i ∈ effInputs M (gateAt C j) j := by simp [effInputs, hop, hi, hlt]
      simp [hx, hy, hlt, hag i hmem]
    · simp [hx, hy, hlt]
  · congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hlt : i < M + j
    · have hmem : i ∈ effInputs M (gateAt C j) j := by simp [effInputs, hop, hi, hlt]
      simp [hx, hy, hlt, hag i hmem]
    · simp [hx, hy, hlt]

def effConeStep (M : ℕ) (cs : List (List ℕ)) (g : Gate) : List (List ℕ) :=
  let j := cs.length
  cs ++ [((effInputs M g j).filter (fun w => decide (M ≤ w))).flatMap
    (fun w => (w - M) :: cs.getD (w - M) [])]

def effCones (M : ℕ) (C : Circuit) : List (List ℕ) :=
  C.gates.foldl (effConeStep M) []

def EffInCone (M : ℕ) (C : Circuit) (i j : ℕ) : Prop :=
  i ∈ (effCones M C).getD j []

theorem effCones_length (M : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (effConeStep M) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, effConeStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_foldl_effConeStep_lt (M : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (effConeStep M) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : j < (effConeStep M acc g).length := by
      simp only [effConeStep, List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih (effConeStep M acc g) hlt]
    simp only [effConeStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem effCones_getD_eq (M : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (effCones M C).getD j [] =
      ((effInputs M (gateAt C j) j).filter (fun w => decide (M ≤ w))).flatMap
        (fun w => (w - M) :: (effCones M C).getD (w - M) []) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  have hgate : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate]
  let pre := (C.gates.take j).foldl (effConeStep M) []
  have hpre_len : pre.length = j := by
    simp [pre, effCones_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hc : effCones M C = (C.gates.drop (j + 1)).foldl (effConeStep M) (effConeStep M pre C.gates[j]) := by
    unfold effCones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlt_step : j < (effConeStep M pre C.gates[j]).length := by
    simp only [effConeStep, List.length_append, List.length_cons, List.length_nil, hpre_len]; omega
  rw [hc, getD_foldl_effConeStep_lt _ _ _ _ hlt_step]
  simp only [effConeStep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hpre_len, Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hw_lt : w < M + j := effInputs_lt M C.gates[j] j w hw.1
  have hsub : w - M < pre.length := by omega
  have hsub_s : w - M < (effConeStep M pre C.gates[j]).length := by
    simp only [effConeStep, List.length_append, List.length_cons, List.length_nil]; omega
  congr 1
  have h1 := getD_foldl_effConeStep_lt M (C.gates.drop (j + 1)) (effConeStep M pre C.gates[j]) (w - M) hsub_s
  simp only [effConeStep, hpre_len, List.getD_eq_getElem?_getD] at h1
  rw [h1, List.getElem?_append_left hsub]

theorem effInCone_iff (M : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    EffInCone M C i j ↔
      ∃ w ∈ effInputs M (gateAt C j) j, M ≤ w ∧ (i = w - M ∨ EffInCone M C i (w - M)) := by
  unfold EffInCone
  rw [effCones_getD_eq M C j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2⟩, h3⟩; exact ⟨w, hw1, hw2, h3⟩
  · rintro ⟨w, hw1, hw2, h3⟩; exact ⟨w, ⟨hw1, hw2⟩, h3⟩

theorem effInCone_lt (M : ℕ) (C : Circuit) : ∀ j < C.gates.length, ∀ i, EffInCone M C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj i hij
    rw [effInCone_iff M C i j hj] at hij
    obtain ⟨w, hw, hw1, rfl | hrec⟩ := hij
    · have := effInputs_lt M (gateAt C j) j w hw; omega
    · have hw_lt := effInputs_lt M (gateAt C j) j w hw
      have hsub := ih (w - M) (by omega) (by omega) i hrec
      omega

theorem effInCone_trans (M : ℕ) (C : Circuit) :
    ∀ k < C.gates.length, ∀ i j, EffInCone M C i j → EffInCone M C j k → EffInCone M C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i j hij hjk
    rw [effInCone_iff M C j k hk] at hjk
    obtain ⟨w, hwin, hw1, rfl | hrec⟩ := hjk
    · rw [effInCone_iff M C i k hk]
      exact ⟨w, hwin, hw1, Or.inr hij⟩
    · have hw_lt := effInputs_lt M (gateAt C k) k w hwin
      have hsub := ih (w - M) (by omega) (by omega) i j hij hrec
      rw [effInCone_iff M C i k hk]
      exact ⟨w, hwin, hw1, Or.inr hsub⟩

theorem effInCone_has_reader (M : ℕ) (C : Circuit) :
    ∀ r < C.gates.length, ∀ i, EffInCone M C i r →
      ∃ j, (j = r ∨ EffInCone M C j r) ∧ (M + i) ∈ effInputs M (gateAt C j) j := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr i hir
    rw [effInCone_iff M C i r hr] at hir
    obtain ⟨w, hwin, hw1, hEq | hrec⟩ := hir
    · refine ⟨r, Or.inl rfl, ?_⟩
      have : w = M + i := by omega
      rwa [← this]
    · have hw_lt := effInputs_lt M (gateAt C r) r w hwin
      obtain ⟨j, hjpos, hjin⟩ := ih (w - M) (by omega) (by omega) i hrec
      have hcw : EffInCone M C (w - M) r := (effInCone_iff M C (w - M) r hr).mpr ⟨w, hwin, hw1, Or.inl rfl⟩
      refine ⟨j, ?_, hjin⟩
      rcases hjpos with rfl | hjc
      · exact Or.inr hcw
      · exact Or.inr (effInCone_trans M C r hr j (w - M) hjc hcw)

theorem wireVal_eq_on_cone (M : ℕ) (C : Circuit) (gout : ℕ) (hgout : gout < C.gates.length)
    (xs ys : List Bool) (hx : xs.length = M) (hy : ys.length = M)
    (hag : ∀ j, (j = gout ∨ EffInCone M C j gout) →
      ∀ w ∈ effInputs M (gateAt C j) j, w < M → xs.getD w false = ys.getD w false) :
    ∀ j, (j = gout ∨ EffInCone M C j gout) → wireVal C xs (M + j) = wireVal C ys (M + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjg
    have hj : j < C.gates.length := by
      rcases hjg with rfl | hc
      · exact hgout
      · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
    apply wireVal_gate_eq_of_eff C xs ys M j hx hy hj
    intro w hw
    by_cases hlt : w < M
    · rw [wireVal_lt C xs w (by omega), wireVal_lt C ys w (by omega)]
      exact hag j hjg w hw hlt
    · have hw_lt := effInputs_lt M (gateAt C j) j w hw
      have hcw : EffInCone M C (w - M) j :=
        (effInCone_iff M C (w - M) j hj).mpr ⟨w, hw, by omega, Or.inl rfl⟩
      have hcg : EffInCone M C (w - M) gout := by
        rcases hjg with rfl | hc
        · exact hcw
        · exact effInCone_trans M C gout hgout (w - M) j hcw hc
      have heq : w = M + (w - M) := by omega
      rw [heq]
      exact ih (w - M) (by omega) (Or.inr hcg)

theorem gateOp_eval_mono_map (op : GateOp) (hop : op = .and ∨ op = .or) (l : List ℕ) (f1 f2 : ℕ → Bool)
    (h : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    rintro hall _ ⟨i, hi, rfl⟩
    exact h i hi (hall (f1 i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h1⟩
    exact ⟨f2 i, ⟨i, hi, rfl⟩, h i hi h1⟩

theorem wireVal_mono_no_not (M : ℕ) (C : Circuit) (gout : ℕ) (hgout : gout < C.gates.length)
    (hfan : FanInTwo C)
    (hno_not : ∀ j, (j = gout ∨ EffInCone M C j gout) → (gateAt C j).op ≠ .not)
    (xs ys : List Bool) (hx : xs.length = M) (hy : ys.length = M)
    (hle : ∀ j, (j = gout ∨ EffInCone M C j gout) →
      ∀ w ∈ effInputs M (gateAt C j) j, w < M → xs.getD w false = true → ys.getD w false = true) :
    ∀ j, (j = gout ∨ EffInCone M C j gout) → wireVal C xs (M + j) = true → wireVal C ys (M + j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjg hval
    have hj : j < C.gates.length := by
      rcases hjg with rfl | hc
      · exact hgout
      · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
    have hmem_g : gateAt C j ∈ C.gates := by
      simp [gateAt, List.getD_eq_getElem?_getD, hj, List.getElem_mem]
    have hop_set := (hfan _ hmem_g).1
    have hnot_j := hno_not j hjg
    have hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop_set
      rcases hop_set with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hnot_j
    have hx_eq : M + j = xs.length + j := by omega
    have hy_eq : M + j = ys.length + j := by omega
    rw [hx_eq, wireVal_gate_raw C xs j hj] at hval
    rw [hy_eq, wireVal_gate_raw C ys j hj]
    apply gateOp_eval_mono_map (gateAt C j).op hop (gateAt C j).inputs _ _ _ hval
    intro i hi h1
    by_cases hlt : i < M + j
    · simp only [hx, hy, hlt, ite_true] at h1 ⊢
      have heff : i ∈ effInputs M (gateAt C j) j := by
        rcases hop with h | h <;> simp [effInputs, h, hi, hlt]
      by_cases hiM : i < M
      · rw [wireVal_lt C xs i (by omega)] at h1
        rw [wireVal_lt C ys i (by omega)]
        exact hle j hjg i heff hiM h1
      · have hcw : EffInCone M C (i - M) j :=
          (effInCone_iff M C (i - M) j hj).mpr ⟨i, heff, by omega, Or.inl rfl⟩
        have hcg : EffInCone M C (i - M) gout := by
          rcases hjg with rfl | hc
          · exact hcw
          · exact effInCone_trans M C gout hgout (i - M) j hcw hc
        have heq : i = M + (i - M) := by omega
        rw [heq] at h1 ⊢
        exact ih (i - M) (by omega) (Or.inr hcg) h1
    · simp only [hx, hlt, ite_false] at h1
      cases h1

theorem disjoint_of_card_biUnion_eq_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (F : α → Finset β) (heq : (S.biUnion F).card = ∑ j ∈ S, (F j).card) :
    ∀ j1 ∈ S, ∀ j2 ∈ S, j1 ≠ j2 → Disjoint (F j1) (F j2) := by
  intro j1 hj1 j2 hj2 hne
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  let S' := S.erase j1
  have hj2' : j2 ∈ S' := Finset.mem_erase.mpr ⟨hne.symm, hj2⟩
  have hS_ins : insert j1 S' = S := Finset.insert_erase hj1
  have hsum : ∑ j ∈ S, (F j).card = (F j1).card + ∑ j ∈ S', (F j).card :=
    (Finset.add_sum_erase S (fun j => (F j).card) hj1).symm
  have hbiu : S.biUnion F = F j1 ∪ S'.biUnion F := by
    conv_lhs => rw [← hS_ins]
    exact Finset.biUnion_insert
  have hcard_u := Finset.card_union_add_card_inter (F j1) (S'.biUnion F)
  have hinter_pos : 1 ≤ (F j1 ∩ S'.biUnion F).card := by
    apply Finset.card_pos.mpr
    exact ⟨w, Finset.mem_inter.mpr ⟨hw1, Finset.mem_biUnion.mpr ⟨j2, hj2', hw2⟩⟩⟩
  have hle_s' : (S'.biUnion F).card ≤ ∑ j ∈ S', (F j).card := Finset.card_biUnion_le
  rw [hbiu] at heq
  omega

theorem wireVal_unate_one_not (M : ℕ) (C : Circuit) (gout g0 : ℕ)
    (hgout : gout < C.gates.length) (hfan : FanInTwo C)
    (hg0_cone : g0 = gout ∨ EffInCone M C g0 gout)
    (hg0_not : (gateAt C g0).op = .not)
    (huniq_not : ∀ j, (j = gout ∨ EffInCone M C j gout) → (gateAt C j).op = .not → j = g0)
    (hdisj_eff : ∀ j1 j2, (j1 = gout ∨ EffInCone M C j1 gout) → (j2 = gout ∨ EffInCone M C j2 gout) →
      j1 ≠ j2 → ∀ w, w ∈ effInputs M (gateAt C j1) j1 → w ∉ effInputs M (gateAt C j2) j2)
    (xs ys : List Bool) (hx : xs.length = M) (hy : ys.length = M)
    (hInNot : ∀ w < M, (∃ j, (j = g0 ∨ EffInCone M C j g0) ∧ w ∈ effInputs M (gateAt C j) j) →
      ys.getD w false = true → xs.getD w false = true)
    (hOutNot : ∀ w < M, (∃ j, (j = gout ∨ EffInCone M C j gout) ∧ w ∈ effInputs M (gateAt C j) j) →
      ¬ (∃ j, (j = g0 ∨ EffInCone M C j g0) ∧ w ∈ effInputs M (gateAt C j) j) →
      xs.getD w false = true → ys.getD w false = true) :
    ∀ j, (j = gout ∨ EffInCone M C j gout) →
      (EffInCone M C j g0 → wireVal C ys (M + j) = true → wireVal C xs (M + j) = true) ∧
      (¬ EffInCone M C j g0 → wireVal C xs (M + j) = true → wireVal C ys (M + j) = true) := by
  have hg0_lt : g0 < C.gates.length := by
    rcases hg0_cone with rfl | hc
    · exact hgout
    · exact Nat.lt_trans (effInCone_lt M C gout hgout g0 hc) hgout
  have hbelow_in_cone : ∀ j, (j = g0 ∨ EffInCone M C j g0) → (j = gout ∨ EffInCone M C j gout) := by
    intro j hj
    rcases hj with rfl | hc
    · exact hg0_cone
    · rcases hg0_cone with rfl | hg0c
      · exact Or.inr hc
      · exact Or.inr (effInCone_trans M C gout hgout j g0 hc hg0c)
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjg
    have hj : j < C.gates.length := by
      rcases hjg with rfl | hc
      · exact hgout
      · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
    have hmem_g : gateAt C j ∈ C.gates := by
      simp [gateAt, List.getD_eq_getElem?_getD, hj, List.getElem_mem]
    have hop_set := (hfan _ hmem_g).1
    have hx_eq : M + j = xs.length + j := by omega
    have hy_eq : M + j = ys.length + j := by omega
    constructor
    · intro hcj hval
      have hj_ne_g0 : j ≠ g0 := by
        have := effInCone_lt M C g0 hg0_lt j hcj; omega
      have hnot_j : (gateAt C j).op ≠ .not := fun h => hj_ne_g0 (huniq_not j hjg h)
      have hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop_set
        rcases hop_set with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hnot_j
      rw [hy_eq, wireVal_gate_raw C ys j hj] at hval
      rw [hx_eq, wireVal_gate_raw C xs j hj]
      apply gateOp_eval_mono_map (gateAt C j).op hop (gateAt C j).inputs _ _ _ hval
      intro i hi h1
      by_cases hlt : i < M + j
      · simp only [hx, hy, hlt, ite_true] at h1 ⊢
        have heff : i ∈ effInputs M (gateAt C j) j := by
          rcases hop with h | h <;> simp [effInputs, h, hi, hlt]
        by_cases hiM : i < M
        · rw [wireVal_lt C ys i (by omega)] at h1
          rw [wireVal_lt C xs i (by omega)]
          exact hInNot i hiM ⟨j, Or.inr hcj, heff⟩ h1
        · have hckj : EffInCone M C (i - M) j :=
            (effInCone_iff M C (i - M) j hj).mpr ⟨i, heff, by omega, Or.inl rfl⟩
          have hckg0 : EffInCone M C (i - M) g0 := effInCone_trans M C g0 hg0_lt (i - M) j hckj hcj
          have hckg : (i - M) = gout ∨ EffInCone M C (i - M) gout := hbelow_in_cone (i - M) (Or.inr hckg0)
          have heq : i = M + (i - M) := by omega
          rw [heq] at h1 ⊢
          exact (ih (i - M) (by omega) hckg).1 hckg0 h1
      · simp only [hy, hlt, ite_false] at h1
        cases h1
    · intro hncj hval
      by_cases hjg0 : j = g0
      · subst hjg0
        rw [hx_eq, wireVal_gate_raw C xs j hj] at hval
        rw [hy_eq, wireVal_gate_raw C ys j hj]
        simp only [hg0_not, GateOp.eval] at hval ⊢
        cases hins : (gateAt C j).inputs with
        | nil => simp
        | cons a t =>
          simp only [List.map_cons, List.headD_cons] at hval ⊢
          by_cases hlt : a < M + j
          · simp only [hx, hy, hlt, ite_true] at hval ⊢
            have heff : a ∈ effInputs M (gateAt C j) j := by
              simp [effInputs, hg0_not, hins, hlt]
            have hle_a : wireVal C ys a = true → wireVal C xs a = true := by
              by_cases haM : a < M
              · intro hya
                rw [wireVal_lt C ys a (by omega)] at hya
                rw [wireVal_lt C xs a (by omega)]
                exact hInNot a haM ⟨j, Or.inl rfl, heff⟩ hya
              · intro hya
                have hck : EffInCone M C (a - M) j :=
                  (effInCone_iff M C (a - M) j hj).mpr ⟨a, heff, by omega, Or.inl rfl⟩
                have hckg : (a - M) = gout ∨ EffInCone M C (a - M) gout := hbelow_in_cone (a - M) (Or.inr hck)
                have heq : a = M + (a - M) := by omega
                rw [heq] at hya ⊢
                exact (ih (a - M) (by omega) hckg).1 hck hya
            cases hxa : wireVal C xs a <;> cases hya : wireVal C ys a <;> simp_all
          · simp only [hy, hlt, ite_false]
            rfl
      · have hnot_j : (gateAt C j).op ≠ .not := fun h => hjg0 (huniq_not j hjg h)
        have hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop_set
          rcases hop_set with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hnot_j
        rw [hx_eq, wireVal_gate_raw C xs j hj] at hval
        rw [hy_eq, wireVal_gate_raw C ys j hj]
        apply gateOp_eval_mono_map (gateAt C j).op hop (gateAt C j).inputs _ _ _ hval
        intro i hi h1
        by_cases hlt : i < M + j
        · simp only [hx, hy, hlt, ite_true] at h1 ⊢
          have heff : i ∈ effInputs M (gateAt C j) j := by
            rcases hop with h | h <;> simp [effInputs, h, hi, hlt]
          by_cases hiM : i < M
          · rw [wireVal_lt C xs i (by omega)] at h1
            rw [wireVal_lt C ys i (by omega)]
            have hnot_in : ¬ (∃ j1, (j1 = g0 ∨ EffInCone M C j1 g0) ∧ i ∈ effInputs M (gateAt C j1) j1) := by
              rintro ⟨j1, hj1b, hi1⟩
              have hj1_ne : j1 ≠ j := by
                intro heq; subst heq
                rcases hj1b with rfl | hc
                · exact hjg0 rfl
                · exact hncj hc
              exact hdisj_eff j1 j (hbelow_in_cone j1 hj1b) hjg hj1_ne i hi1 heff
            exact hOutNot i hiM ⟨j, hjg, heff⟩ hnot_in h1
          · have hckj : EffInCone M C (i - M) j :=
              (effInCone_iff M C (i - M) j hj).mpr ⟨i, heff, by omega, Or.inl rfl⟩
            have hckg : (i - M) = gout ∨ EffInCone M C (i - M) gout := by
              rcases hjg with rfl | hc
              · exact Or.inr hckj
              · exact Or.inr (effInCone_trans M C gout hgout (i - M) j hckj hc)
            have hnot_ckg0 : ¬ EffInCone M C (i - M) g0 := by
              intro hckg0
              obtain ⟨j1, hj1b, hi1⟩ := effInCone_has_reader M C g0 hg0_lt (i - M) hckg0
              have hj1_ne : j1 ≠ j := by
                intro heq; subst heq
                rcases hj1b with rfl | hc
                · exact hjg0 rfl
                · exact hncj hc
              have heq_i : M + (i - M) = i := by omega
              rw [heq_i] at hi1
              exact hdisj_eff j1 j (hbelow_in_cone j1 hj1b) hjg hj1_ne i hi1 heff
            have heq : i = M + (i - M) := by omega
            rw [heq] at h1 ⊢
            exact (ih (i - M) (by omega) hckg).2 hnot_ckg0 h1
        · simp only [hx, hlt, ite_false] at h1
          cases h1

theorem len_oneEach (N : ℕ) (u v : Fin N) : (oneEach u v).length = 2 * N := by
  simp [oneEach]; omega

theorem getD_oneEach (N : ℕ) (u v : Fin N) (w : ℕ) :
    (oneEach u v).getD w false = (decide (w = u.val) || decide (w = N + v.val)) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  by_cases h1 : w < N
  · rw [List.getElem?_append_left (by simp [h1]), List.getElem?_ofFn]
    simp only [h1, dite_true, Option.getD_some]
    have hne : w ≠ N + v.val := by omega
    simp [Fin.ext_iff, hne]
  · by_cases h2 : w < 2 * N
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem?_ofFn]
      have hsub : w - N < N := by omega
      simp only [hsub, dite_true, Option.getD_some]
      have hne : w ≠ u.val := by omega
      have heq : (w - N = v.val) ↔ (w = N + v.val) := by omega
      simp [Fin.ext_iff, hne, heq]
    · rw [List.getElem?_eq_none (by simp; omega)]
      have hne1 : w ≠ u.val := by omega
      have hne2 : w ≠ N + v.val := by omega
      simp [hne1, hne2]

theorem main_bound : ∀ (N : ℕ), 2 ≤ N → ∀ (C : Circuit), FanInTwo C →
    Represents (fun u v : Fin N => decide (u = v)) C → 2 * N - 1 ≤ C.size := by
  intro N hN C hfan hrep
  classical
  let M := 2 * N
  let f0 : Fin N := ⟨0, by omega⟩
  let f1 : Fin N := ⟨1, by omega⟩
  have hf01 : f0 ≠ f1 := by simp [f0, f1, Fin.ext_iff]
  have hout_ge : M ≤ C.output := by
    by_contra hlt
    push Not at hlt
    by_cases hltN : C.output < N
    · let u0 : Fin N := ⟨C.output, hltN⟩
      let v0 : Fin N := if u0.val = 0 then f1 else f0
      have huv_ne : u0 ≠ v0 := by
        simp only [v0]
        split_ifs with h0
        · intro heq; have := congrArg Fin.val heq; simp [f1] at this; omega
        · intro heq; have := congrArg Fin.val heq; simp [f0] at this; omega
      have hsame : ∀ v : Fin N, C.eval (oneEach u0 v) = true := by
        intro v
        change wireVal C (oneEach u0 v) C.output = true
        rw [wireVal_lt C _ _ (by rw [len_oneEach]; exact hlt), getD_oneEach]
        simp [u0]
      have h1 := hsame u0; rw [hrep] at h1
      have h2 := hsame v0; rw [hrep] at h2
      simp [huv_ne] at h2
    · let v0 : Fin N := ⟨C.output - N, by omega⟩
      let u0 : Fin N := if v0.val = 0 then f1 else f0
      have huv_ne : u0 ≠ v0 := by
        simp only [u0]
        split_ifs with h0
        · intro heq; have := congrArg Fin.val heq; simp [f1] at this; omega
        · intro heq; have := congrArg Fin.val heq; simp [f0] at this; omega
      have hsame : ∀ u : Fin N, C.eval (oneEach u v0) = true := by
        intro u
        change wireVal C (oneEach u v0) C.output = true
        rw [wireVal_lt C _ _ (by rw [len_oneEach]; exact hlt), getD_oneEach]
        have : C.output = N + v0.val := by simp [v0]; omega
        simp [this]
      have h1 := hsame v0; rw [hrep] at h1
      have h2 := hsame u0; rw [hrep] at h2
      simp [huv_ne] at h2
  have hout_lt : C.output < M + C.gates.length := by
    by_contra hge
    push Not at hge
    have hall_f : ∀ u v : Fin N, C.eval (oneEach u v) = false := by
      intro u v
      change wireVal C (oneEach u v) C.output = false
      exact wireVal_ge C _ _ (by rw [len_oneEach]; exact hge)
    have h1 := hall_f f0 f0; rw [hrep] at h1
    have h2 := hall_f f0 f1; rw [hrep] at h2
    simp at h1
  let gout := C.output - M
  have hgout : gout < C.gates.length := by omega
  have hout_eq : C.output = M + gout := by omega
  let S : Finset ℕ := (Finset.range C.gates.length).filter (fun j => j = gout ∨ EffInCone M C j gout)
  have hgout_S : gout ∈ S := by simp [S, hgout]
  have hS_le : S.card ≤ C.size := by
    calc
      S.card ≤ (Finset.range C.gates.length).card := Finset.card_filter_le _ _
      _ = C.size := by simp [Circuit.size]
  let E_in : Finset ℕ := (Finset.range M).filter (fun w => ∃ j ∈ S, w ∈ effInputs M (gateAt C j) j)
  let E_gate : Finset ℕ := (S.erase gout).image (fun i => M + i)
  have hE_gate_card : E_gate.card = S.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_erase_of_mem hgout_S]
  have hdisj : Disjoint E_in E_gate := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [E_in, Finset.mem_filter, Finset.mem_range] at h1
    simp only [E_gate, Finset.mem_image] at h2
    obtain ⟨i, _, rfl⟩ := h2
    omega
  let F : ℕ → Finset ℕ := fun j => (effInputs M (gateAt C j) j).toFinset
  have hsub : E_in ∪ E_gate ⊆ S.biUnion F := by
    intro w hw
    rw [Finset.mem_union] at hw
    rw [Finset.mem_biUnion]
    rcases hw with h1 | h2
    · simp only [E_in, Finset.mem_filter, Finset.mem_range] at h1
      obtain ⟨_, j, hjS, hjw⟩ := h1
      exact ⟨j, hjS, List.mem_toFinset.mpr hjw⟩
    · simp only [E_gate, Finset.mem_image, Finset.mem_erase] at h2
      obtain ⟨i, ⟨hi_ne, hiS⟩, rfl⟩ := h2
      simp only [S, Finset.mem_filter, Finset.mem_range] at hiS
      have hci : EffInCone M C i gout := hiS.2.resolve_left hi_ne
      obtain ⟨j, hjpos, hjin⟩ := effInCone_has_reader M C gout hgout i hci
      have hj_lt : j < C.gates.length := by
        rcases hjpos with rfl | hc
        · exact hgout
        · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
      have hjS : j ∈ S := by simp [S, hj_lt, hjpos]
      exact ⟨j, hjS, List.mem_toFinset.mpr hjin⟩
  have hcard_eu : E_in.card + (S.card - 1) = (E_in ∪ E_gate).card := by
    rw [Finset.card_union_of_disjoint hdisj, hE_gate_card]
  have hle_biu : (E_in ∪ E_gate).card ≤ (S.biUnion F).card := Finset.card_le_card hsub
  have hbiu_le_sumF : (S.biUnion F).card ≤ ∑ j ∈ S, (F j).card := Finset.card_biUnion_le
  have hsumF_le_len : ∑ j ∈ S, (F j).card ≤ ∑ j ∈ S, (effInputs M (gateAt C j) j).length :=
    Finset.sum_le_sum (fun j _ => List.toFinset_card_le _)
  let S_not : Finset ℕ := S.filter (fun j => (gateAt C j).op = .not)
  have hsum_not_bound : (∑ j ∈ S, (effInputs M (gateAt C j) j).length) + S_not.card ≤ 2 * S.card := by
    have hcard_not : S_not.card = ∑ j ∈ S, (if (gateAt C j).op = .not then 1 else 0) :=
      Finset.card_filter _ _
    rw [hcard_not, ← Finset.sum_add_distrib]
    calc
      ∑ j ∈ S, ((effInputs M (gateAt C j) j).length + if (gateAt C j).op = .not then 1 else 0)
          ≤ ∑ _j ∈ S, 2 := by
            apply Finset.sum_le_sum
            intro j hjS
            simp only [S, Finset.mem_filter, Finset.mem_range] at hjS
            have hmem : gateAt C j ∈ C.gates := by
              simp [gateAt, List.getD_eq_getElem?_getD, hjS.1, List.getElem_mem]
            by_cases hnot : (gateAt C j).op = .not
            · simp only [hnot, ite_true]
              have := effInputs_not_len_le M (gateAt C j) j hnot
              omega
            · simp only [hnot, ite_false, add_zero]
              exact effInputs_len_le M (gateAt C j) j (hfan _ hmem).2
      _ = 2 * S.card := by simp [Nat.mul_comm]
  let R_read : Finset (Fin N) := Finset.univ.filter (fun u => u.val ∈ E_in)
  let C_read : Finset (Fin N) := Finset.univ.filter (fun v => N + v.val ∈ E_in)
  have hR_miss : ∀ u1 u2 : Fin N, u1.val ∉ E_in → u2.val ∉ E_in → u1 = u2 := by
    intro u1 u2 h1 h2
    by_contra hne
    have heq : wireVal C (oneEach u1 u1) (M + gout) = wireVal C (oneEach u2 u1) (M + gout) := by
      apply wireVal_eq_on_cone M C gout hgout _ _ (len_oneEach N u1 u1) (len_oneEach N u2 u1)
      · intro j hjg w hw hwM
        have hj_lt : j < C.gates.length := by
          rcases hjg with rfl | hc
          · exact hgout
          · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
        have hwE : w ∈ E_in := by simp [E_in, hwM]; exact ⟨j, by simp [S, hj_lt, hjg], hw⟩
        rw [getD_oneEach, getD_oneEach]
        have hne1 : w ≠ u1.val := fun he => h1 (he ▸ hwE)
        have hne2 : w ≠ u2.val := fun he => h2 (he ▸ hwE)
        simp [hne1, hne2]
      · exact Or.inl rfl
    rw [← hout_eq] at heq
    change C.eval (oneEach u1 u1) = C.eval (oneEach u2 u1) at heq
    rw [hrep, hrep] at heq
    simp [Ne.symm hne] at heq
  have hC_miss : ∀ v1 v2 : Fin N, N + v1.val ∉ E_in → N + v2.val ∉ E_in → v1 = v2 := by
    intro v1 v2 h1 h2
    by_contra hne
    have heq : wireVal C (oneEach v1 v1) (M + gout) = wireVal C (oneEach v1 v2) (M + gout) := by
      apply wireVal_eq_on_cone M C gout hgout _ _ (len_oneEach N v1 v1) (len_oneEach N v1 v2)
      · intro j hjg w hw hwM
        have hj_lt : j < C.gates.length := by
          rcases hjg with rfl | hc
          · exact hgout
          · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
        have hwE : w ∈ E_in := by simp [E_in, hwM]; exact ⟨j, by simp [S, hj_lt, hjg], hw⟩
        rw [getD_oneEach, getD_oneEach]
        have hne1 : w ≠ N + v1.val := fun he => h1 (he ▸ hwE)
        have hne2 : w ≠ N + v2.val := fun he => h2 (he ▸ hwE)
        simp [hne1, hne2]
      · exact Or.inl rfl
    rw [← hout_eq] at heq
    change C.eval (oneEach v1 v1) = C.eval (oneEach v1 v2) at heq
    rw [hrep, hrep] at heq
    simp [hne] at heq
  have hR_card : N - 1 ≤ R_read.card := by
    have hcomp : (Finset.univ \ R_read).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, R_read, Finset.mem_filter] at ha hb
      exact hR_miss a b ha hb
    have hadd : (Finset.univ \ R_read).card + R_read.card = N := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hC_card : N - 1 ≤ C_read.card := by
    have hcomp : (Finset.univ \ C_read).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, C_read, Finset.mem_filter] at ha hb
      exact hC_miss a b ha hb
    have hadd : (Finset.univ \ C_read).card + C_read.card = N := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hE_in_eq : E_in.card = R_read.card + C_read.card := by
    let imgR : Finset ℕ := R_read.image Fin.val
    let imgC : Finset ℕ := C_read.image (fun v => N + v.val)
    have hdisj_rc : Disjoint imgR imgC := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [imgR, Finset.mem_image] at h1
      simp only [imgC, Finset.mem_image] at h2
      obtain ⟨u, _, rfl⟩ := h1; obtain ⟨v, _, hv⟩ := h2; omega
    have heq_rc : imgR ∪ imgC = E_in := by
      ext w
      simp only [Finset.mem_union, imgR, imgC, Finset.mem_image, R_read, C_read, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩)
        · exact hu
        · exact hv
      · intro hwE
        have hwM : w < M := (Finset.mem_range.mp (Finset.mem_filter.mp hwE).1)
        by_cases hwN : w < N
        · exact Or.inl ⟨⟨w, hwN⟩, hwE, rfl⟩
        · exact Or.inr ⟨⟨w - N, by omega⟩, by simpa [show N + (w - N) = w by omega] using hwE, by dsimp; omega⟩
    have h1 : imgR.card = R_read.card := Finset.card_image_of_injective _ Fin.val_injective
    have h2 : imgC.card = C_read.card := Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
    rw [← heq_rc, Finset.card_union_of_disjoint hdisj_rc, h1, h2]
  have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨gout, hgout_S⟩
  have hE_in_ge : 2 * N - 2 ≤ E_in.card := by omega
  by_contra hlt_size
  push Not at hlt_size
  have hS_small : S.card ≤ 2 * N - 2 := by omega
  have hS_not_le1 : S_not.card ≤ 1 := by omega
  by_cases hnot0 : S_not.card = 0
  · have hno_not : ∀ j, (j = gout ∨ EffInCone M C j gout) → (gateAt C j).op ≠ .not := by
      intro j hjg hnot
      have hj_lt : j < C.gates.length := by
        rcases hjg with rfl | hc
        · exact hgout
        · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
      have hj_not : j ∈ S_not := by simp [S_not, S, hj_lt, hjg, hnot]
      have := Finset.card_pos.mpr ⟨j, hj_not⟩
      omega
    have hE_lt : E_in.card < 2 * N := by omega
    have hmiss : R_read.card < N ∨ C_read.card < N := by omega
    rcases hmiss with hR_lt | hC_lt
    · have hne_empty : (Finset.univ \ R_read).Nonempty := by
        apply Finset.card_pos.mp
        have hadd : (Finset.univ \ R_read).card + R_read.card = N := by
          rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨u0, hu0⟩ := hne_empty
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, R_read, Finset.mem_filter] at hu0
      let u1 : Fin N := if u0.val = 0 then f1 else f0
      have hu1_ne : u1 ≠ u0 := by
        simp only [u1]
        split_ifs with h0
        · intro h; have := congrArg Fin.val h; simp [f1] at this; omega
        · intro h; have := congrArg Fin.val h; simp [f0] at this; omega
      have htrue : wireVal C (oneEach u0 u0) (M + gout) = true := by
        rw [← hout_eq]; change C.eval (oneEach u0 u0) = true; rw [hrep]; simp
      have hmono : wireVal C (oneEach u1 u0) (M + gout) = true := by
        apply wireVal_mono_no_not M C gout hgout hfan hno_not (oneEach u0 u0) (oneEach u1 u0)
          (len_oneEach N u0 u0) (len_oneEach N u1 u0)
        · intro j hjg w hw hwM h1
          have hj_lt : j < C.gates.length := by
            rcases hjg with rfl | hc
            · exact hgout
            · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
          have hwE : w ∈ E_in := by simp [E_in, hwM]; exact ⟨j, by simp [S, hj_lt, hjg], hw⟩
          rw [getD_oneEach] at h1 ⊢
          have hne_u0 : w ≠ u0.val := fun he => hu0 (he ▸ hwE)
          simp only [hne_u0, decide_false, Bool.false_or] at h1
          simp [h1]
        · exact Or.inl rfl
        · exact htrue
      rw [← hout_eq] at hmono
      change C.eval (oneEach u1 u0) = true at hmono
      rw [hrep] at hmono
      simp [hu1_ne] at hmono
    · have hne_empty : (Finset.univ \ C_read).Nonempty := by
        apply Finset.card_pos.mp
        have hadd : (Finset.univ \ C_read).card + C_read.card = N := by
          rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨v0, hv0⟩ := hne_empty
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, C_read, Finset.mem_filter] at hv0
      let v1 : Fin N := if v0.val = 0 then f1 else f0
      have hv1_ne : v1 ≠ v0 := by
        simp only [v1]
        split_ifs with h0
        · intro h; have := congrArg Fin.val h; simp [f1] at this; omega
        · intro h; have := congrArg Fin.val h; simp [f0] at this; omega
      have htrue : wireVal C (oneEach v0 v0) (M + gout) = true := by
        rw [← hout_eq]; change C.eval (oneEach v0 v0) = true; rw [hrep]; simp
      have hmono : wireVal C (oneEach v0 v1) (M + gout) = true := by
        apply wireVal_mono_no_not M C gout hgout hfan hno_not (oneEach v0 v0) (oneEach v0 v1)
          (len_oneEach N v0 v0) (len_oneEach N v0 v1)
        · intro j hjg w hw hwM h1
          have hj_lt : j < C.gates.length := by
            rcases hjg with rfl | hc
            · exact hgout
            · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
          have hwE : w ∈ E_in := by simp [E_in, hwM]; exact ⟨j, by simp [S, hj_lt, hjg], hw⟩
          rw [getD_oneEach] at h1 ⊢
          have hne_v0 : w ≠ N + v0.val := fun he => hv0 (he ▸ hwE)
          simp only [hne_v0, decide_false, Bool.or_false] at h1
          simp [h1]
        · exact Or.inl rfl
        · exact htrue
      rw [← hout_eq] at hmono
      change C.eval (oneEach v0 v1) = true at hmono
      rw [hrep] at hmono
      simp [Ne.symm hv1_ne] at hmono
  · have hS_not_eq1 : S_not.card = 1 := by omega
    have hE_eq : E_in.card = 2 * N - 2 := by omega
    have hS_eq : S.card = 2 * N - 2 := by omega
    have hbiu_eq_sum : (S.biUnion F).card = ∑ j ∈ S, (F j).card := by omega
    obtain ⟨g0, hg0_eq⟩ := Finset.card_eq_one.mp hS_not_eq1
    have hg0_mem : g0 ∈ S_not := by rw [hg0_eq]; exact Finset.mem_singleton_self g0
    have hg0_S : g0 ∈ S := (Finset.mem_filter.mp hg0_mem).1
    have hg0_not : (gateAt C g0).op = .not := (Finset.mem_filter.mp hg0_mem).2
    have hg0_cone : g0 = gout ∨ EffInCone M C g0 gout := (Finset.mem_filter.mp hg0_S).2
    have huniq_not : ∀ j, (j = gout ∨ EffInCone M C j gout) → (gateAt C j).op = .not → j = g0 := by
      intro j hjg hnot
      have hj_lt : j < C.gates.length := by
        rcases hjg with rfl | hc
        · exact hgout
        · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
      have hj_mem : j ∈ S_not := by simp [S_not, S, hj_lt, hjg, hnot]
      rw [hg0_eq, Finset.mem_singleton] at hj_mem
      exact hj_mem
    have hdisj_F := disjoint_of_card_biUnion_eq_sum S F hbiu_eq_sum
    have hdisj_eff : ∀ j1 j2, (j1 = gout ∨ EffInCone M C j1 gout) → (j2 = gout ∨ EffInCone M C j2 gout) →
        j1 ≠ j2 → ∀ w, w ∈ effInputs M (gateAt C j1) j1 → w ∉ effInputs M (gateAt C j2) j2 := by
      intro j1 j2 hj1 hj2 hne w hw1 hw2
      have hj1_lt : j1 < C.gates.length := by
        rcases hj1 with rfl | hc
        · exact hgout
        · exact Nat.lt_trans (effInCone_lt M C gout hgout j1 hc) hgout
      have hj2_lt : j2 < C.gates.length := by
        rcases hj2 with rfl | hc
        · exact hgout
        · exact Nat.lt_trans (effInCone_lt M C gout hgout j2 hc) hgout
      have h1S : j1 ∈ S := by simp [S, hj1_lt, hj1]
      have h2S : j2 ∈ S := by simp [S, hj2_lt, hj2]
      exact Finset.disjoint_left.mp (hdisj_F j1 h1S j2 h2S hne)
        (List.mem_toFinset.mpr hw1) (List.mem_toFinset.mpr hw2)
    have hR_le : R_read.card ≤ N := by
      calc R_read.card ≤ Finset.univ.card := Finset.card_le_univ _
        _ = N := Fintype.card_fin N
    have hC_le : C_read.card ≤ N := by
      calc C_read.card ≤ Finset.univ.card := Finset.card_le_univ _
        _ = N := Fintype.card_fin N
    have hR_eq : R_read.card = N - 1 := by omega
    have hC_eq : C_read.card = N - 1 := by omega
    obtain ⟨u0, hu0⟩ : (Finset.univ \ R_read).Nonempty := by
      apply Finset.card_pos.mp
      have hadd : (Finset.univ \ R_read).card + R_read.card = N := by
        rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨v0, hv0⟩ : (Finset.univ \ C_read).Nonempty := by
      apply Finset.card_pos.mp
      have hadd : (Finset.univ \ C_read).card + C_read.card = N := by
        rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, R_read, C_read, Finset.mem_filter] at hu0 hv0
    have hngout_g0 : ¬ EffInCone M C gout g0 := by
      intro hc
      rcases hg0_cone with rfl | hg0c
      · have := effInCone_lt M C gout hgout gout hc; omega
      · have h1 := effInCone_lt M C gout hgout g0 hg0c
        have h2 := effInCone_lt M C g0 (Nat.lt_trans h1 hgout) gout hc
        omega
    let InNot : ℕ → Prop := fun w => ∃ j, (j = g0 ∨ EffInCone M C j g0) ∧ w ∈ effInputs M (gateAt C j) j
    have hunate : ∀ xs ys : List Bool, xs.length = M → ys.length = M →
        (∀ w ∈ E_in, InNot w → ys.getD w false = true → xs.getD w false = true) →
        (∀ w ∈ E_in, ¬ InNot w → xs.getD w false = true → ys.getD w false = true) →
        wireVal C xs (M + gout) = true → wireVal C ys (M + gout) = true := by
      intro xs ys hx hy hIn hOut
      refine (wireVal_unate_one_not M C gout g0 hgout hfan hg0_cone hg0_not huniq_not hdisj_eff
        xs ys hx hy ?_ ?_ gout (Or.inl rfl)).2 hngout_g0
      · intro w hwM hInw
        obtain ⟨j, hjb, hwj⟩ := hInw
        have hjc : j = gout ∨ EffInCone M C j gout := by
          rcases hjb with rfl | hc
          · exact hg0_cone
          · rcases hg0_cone with rfl | hg0c
            · exact Or.inr hc
            · exact Or.inr (effInCone_trans M C gout hgout j g0 hc hg0c)
        have hj_lt : j < C.gates.length := by
          rcases hjc with rfl | hc
          · exact hgout
          · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
        have hwE : w ∈ E_in := by simp [E_in, hwM]; exact ⟨j, by simp [S, hj_lt, hjc], hwj⟩
        exact hIn w hwE ⟨j, hjb, hwj⟩
      · intro w hwM hex hNotIn
        obtain ⟨j, hjc, hwj⟩ := hex
        have hj_lt : j < C.gates.length := by
          rcases hjc with rfl | hc
          · exact hgout
          · exact Nat.lt_trans (effInCone_lt M C gout hgout j hc) hgout
        have hwE : w ∈ E_in := by simp [E_in, hwM]; exact ⟨j, by simp [S, hj_lt, hjc], hwj⟩
        exact hOut w hwE hNotIn
    have hstep_eval : ∀ a1 b1 a2 b2 : Fin N,
        (∀ w ∈ E_in, InNot w → (oneEach a2 b2).getD w false = true → (oneEach a1 b1).getD w false = true) →
        (∀ w ∈ E_in, ¬ InNot w → (oneEach a1 b1).getD w false = true → (oneEach a2 b2).getD w false = true) →
        C.eval (oneEach a1 b1) = true → C.eval (oneEach a2 b2) = true := by
      intro a1 b1 a2 b2 h1 h2 hev
      change wireVal C (oneEach a1 b1) C.output = true at hev
      change wireVal C (oneEach a2 b2) C.output = true
      rw [hout_eq] at hev ⊢
      exact hunate (oneEach a1 b1) (oneEach a2 b2) (len_oneEach N a1 b1) (len_oneEach N a2 b2) h1 h2 hev
    by_cases heq_uv : u0 = v0
    · let u1 : Fin N := if u0.val = 0 then f1 else f0
      have hu1_ne : u1 ≠ u0 := by
        simp only [u1]
        split_ifs with h0
        · intro h; have := congrArg Fin.val h; simp [f1] at this; omega
        · intro h; have := congrArg Fin.val h; simp [f0] at this; omega
      have hu1_v0 : u1 ≠ v0 := heq_uv ▸ hu1_ne
      have hx_in_not : InNot u1.val := by
        by_contra hnotx
        have hbad : C.eval (oneEach u1 u0) = true := by
          apply hstep_eval u0 u0 u1 u0
          · intro w hwE _ h2
            rw [getD_oneEach] at h2 ⊢
            have hne_u0 : w ≠ u0.val := fun he => hu0 (he ▸ hwE)
            have hne_v0 : w ≠ N + u0.val := fun he => hv0 (heq_uv ▸ (he ▸ hwE))
            simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
            rcases h2 with rfl | rfl
            · exact absurd ‹InNot u1.val› hnotx
            · exact absurd rfl hne_v0
          · intro w hwE _ h1
            rw [getD_oneEach] at h1 ⊢
            have hne_u0 : w ≠ u0.val := fun he => hu0 (he ▸ hwE)
            have hne_v0 : w ≠ N + u0.val := fun he => hv0 (heq_uv ▸ (he ▸ hwE))
            simp [hne_u0, hne_v0] at h1
          · rw [hrep]; simp
        rw [hrep] at hbad; simp [hu1_ne] at hbad
      have hy_in_not : InNot (N + u1.val) := by
        by_contra hnoty
        have hbad : C.eval (oneEach u0 u1) = true := by
          apply hstep_eval u0 u0 u0 u1
          · intro w hwE hInw h2
            rw [getD_oneEach] at h2 ⊢
            have hne_u0 : w ≠ u0.val := fun he => hu0 (he ▸ hwE)
            have hne_v0 : w ≠ N + u0.val := fun he => hv0 (heq_uv ▸ (he ▸ hwE))
            simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
            rcases h2 with rfl | rfl
            · exact absurd rfl hne_u0
            · exact absurd hInw hnoty
          · intro w hwE _ h1
            rw [getD_oneEach] at h1 ⊢
            have hne_u0 : w ≠ u0.val := fun he => hu0 (he ▸ hwE)
            have hne_v0 : w ≠ N + u0.val := fun he => hv0 (heq_uv ▸ (he ▸ hwE))
            simp [hne_u0, hne_v0] at h1
          · rw [hrep]; simp
        rw [hrep] at hbad; simp [Ne.symm hu1_ne] at hbad
      have hbad : C.eval (oneEach u1 u0) = true := by
        apply hstep_eval u1 u1 u1 u0
        · intro w hwE _ h2
          rw [getD_oneEach] at h2 ⊢
          have hne_v0 : w ≠ N + u0.val := fun he => hv0 (heq_uv ▸ (he ▸ hwE))
          simp only [hne_v0, decide_false, Bool.or_false] at h2
          simp [h2]
        · intro w hwE hNotIn h1
          rw [getD_oneEach] at h1 ⊢
          simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
          rcases h1 with rfl | rfl
          · exact absurd hx_in_not hNotIn
          · exact absurd hy_in_not hNotIn
        · rw [hrep]; simp
      rw [hrep] at hbad; simp [hu1_ne] at hbad
    · have hx_out_not : ¬ InNot v0.val := by
        intro hinx
        have hbad : C.eval (oneEach u0 v0) = true := by
          apply hstep_eval v0 v0 u0 v0
          · intro w hwE _ h2
            rw [getD_oneEach] at h2
            have hne_u0 : w ≠ u0.val := fun he => hu0 (he ▸ hwE)
            have hne_v0 : w ≠ N + v0.val := fun he => hv0 (he ▸ hwE)
            simp [hne_u0, hne_v0] at h2
          · intro w hwE hNotIn h1
            rw [getD_oneEach] at h1
            have hne_v0 : w ≠ N + v0.val := fun he => hv0 (he ▸ hwE)
            simp only [hne_v0, decide_false, Bool.or_false, decide_eq_true_eq] at h1
            subst h1; exact absurd hinx hNotIn
          · rw [hrep]; simp
        rw [hrep] at hbad; simp [heq_uv] at hbad
      have hbad : C.eval (oneEach v0 u0) = true := by
        apply hstep_eval u0 u0 v0 u0
        · intro w hwE hInw h2
          rw [getD_oneEach] at h2 ⊢
          simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
          rcases h2 with rfl | h2b
          · exact absurd hInw hx_out_not
          · simp [h2b]
        · intro w hwE _ h1
          rw [getD_oneEach] at h1 ⊢
          have hne_u0 : w ≠ u0.val := fun he => hu0 (he ▸ hwE)
          simp only [hne_u0, decide_false, Bool.false_or] at h1
          simp [h1]
        · rw [hrep]; simp
      rw [hrep] at hbad; simp [Ne.symm heq_uv] at hbad

end PEqualNP.Outside.L_meta_17183

theorem PEqualNP.Outside.L_meta_17183 : (∀ (N : ℕ), 2 ≤ N → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin N => decide (u = v)) C → 2 * N - 1 ≤ C.size) := by
  exact PEqualNP.Outside.L_meta_17183.main_bound
