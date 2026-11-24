import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3935
namespace P1
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
inductive Der {α : Type} (op : Fin 4 → α → α → α) : ℕ → Set α → α → Prop
  | here {W : Set α} {y : α} : y ∈ W → Der op 0 W y
  | weak {k : ℕ} {W : Set α} {y : α} : Der op k W y → Der op (k + 1) W y
  | step {k : ℕ} {W : Set α} {y : α} (t : Fin 4) (a b : α) : a ∈ W → b ∈ W →
      Der op k (insert (op t a b) W) y → Der op (k + 1) W y
theorem Der.mono {α : Type} {op : Fin 4 → α → α → α} {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : ∀ {W' : Set α}, W ⊆ W' → Der op k W' y := by
  induction h with
  | here hy => intro W' hs; exact Der.here (hs hy)
  | weak _ ih => intro W' hs; exact Der.weak (ih hs)
  | step t a b ha hb _ ih =>
    intro W' hs
    exact Der.step t a b (hs ha) (hs hb) (ih (Set.insert_subset_insert hs))
theorem Der.le {α : Type} {op : Fin 4 → α → α → α} {k k' : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) (hk : k ≤ k') : Der op k' W y := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Der.weak ih
theorem Der.map {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : Der op' k (e '' W) (e y) := by
  induction h with
  | here hy => exact Der.here ⟨_, hy, rfl⟩
  | weak _ ih => exact Der.weak ih
  | step t a b ha hb _ ih =>
    refine Der.step t (e a) (e b) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ?_
    rwa [Set.image_insert_eq, he] at ih
theorem Der.elim {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) (x : α)
    (hl : ∀ t b, op' t (e x) b = e x ∨ op' t (e x) b = b)
    (hr : ∀ t b, op' t b (e x) = e x ∨ op' t b (e x) = b)
    {k : ℕ} {W : Set α} {y : α} (h : Der op k W y) :
    ∀ U : Set α, W ⊆ insert x U → y ≠ x → e x ∈ e '' U →
      Der op k U y ∨ ∃ k', k = k' + 1 ∧ Der op' k' (e '' U) (e y) := by
  induction h with
  | here hy =>
    intro U hs hne _
    exact Or.inl (Der.here ((hs hy).resolve_left hne))
  | weak _ ih =>
    intro U hs hne hx
    rcases ih U hs hne hx with h | ⟨k', rfl, h⟩
    · exact Or.inl (Der.weak h)
    · exact Or.inr ⟨_, rfl, Der.weak h⟩
  | @step k W y t a b ha hb h ih =>
    intro U hs hne hx
    have im (w : α) (hw : w ∈ W) : e w ∈ e '' U := by
      rcases hs hw with rfl | hw
      · exact hx
      · exact ⟨w, hw, rfl⟩
    by_cases hab : a ∈ U ∧ b ∈ U
    · have hs' : insert (op t a b) W ⊆ insert x (insert (op t a b) U) := by
        rintro w (rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · rcases hs hw with rfl | hw
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hw)
      have hx' : e x ∈ e '' insert (op t a b) U := by
        obtain ⟨u, hu, h⟩ := hx; exact ⟨u, Or.inr hu, h⟩
      rcases ih _ hs' hne hx' with hd | ⟨k', hk', hd⟩
      · exact Or.inl (Der.step t a b hab.1 hab.2 hd)
      · refine Or.inr ⟨k' + 1, by rw [hk'], ?_⟩
        rw [Set.image_insert_eq, he] at hd
        exact Der.step t (e a) (e b) ⟨a, hab.1, rfl⟩ ⟨b, hab.2, rfl⟩ hd
    · have hc : e (op t a b) ∈ e '' U := by
        rw [he]
        by_cases hau : a ∈ U
        · have hbx : b = x := by
            rcases hs hb with h | h
            · exact h
            · exact absurd ⟨hau, h⟩ hab
          subst hbx
          rcases hr t (e a) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im a ha
        · have hax : a = x := by
            rcases hs ha with h | h
            · exact h
            · exact absurd h hau
          subst hax
          rcases hl t (e b) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im b hb
      refine Or.inr ⟨k, rfl, (h.map e he).mono ?_⟩
      rintro _ ⟨w, rfl | hw, rfl⟩
      · exact hc
      · exact im w hw
def opB (t : Fin 4) (a b : Bool) : Bool :=
  match t with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | 3 => b && !a
def opF {Ω : Type} (t : Fin 4) (f g : Ω → Bool) : Ω → Bool := fun x => opB t (f x) (g x)
def opN (t : Fin 4) (a b : ℕ) : ℕ :=
  match t with
  | 0 => Nat.land a b
  | 1 => Nat.lor a b
  | 2 => Nat.xor a (Nat.land a b)
  | 3 => Nat.xor b (Nat.land a b)
lemma land_bit (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i
lemma lor_bit (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i
lemma xor_bit (x y i : ℕ) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simpa [bne] using Nat.testBit_xor x y i
lemma shr_bit (x s i : ℕ) : (Nat.shiftRight x s).testBit i = x.testBit (s + i) := by
  have := Nat.testBit_shiftRight (x := x) (i := s) (j := i)
  simpa using this
lemma opN_bit (t : Fin 4) (a b i : ℕ) :
    (opN t a b).testBit i = opB t (a.testBit i) (b.testBit i) := by
  fin_cases t <;> simp only [opN, opB, land_bit, lor_bit, xor_bit] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl
lemma Der.agree {Ω : Type} {k : ℕ} {W : Set (Ω → Bool)} {y : Ω → Bool} (h : Der opF k W y)
    (p q : Ω) : (∀ w ∈ W, w p = w q) → y p = y q := by
  induction h with
  | here hy => intro hw; exact hw _ hy
  | weak _ ih => exact ih
  | step t a b ha hb _ ih =>
    intro hw
    refine ih ?_
    rintro w (rfl | hm)
    · simp only [opF, hw a ha, hw b hb]
    · exact hw w hm
structure St where
  t : Fin 4
  a : ℕ
  b : ℕ
def St.val (s : St) : ℕ := opN s.t s.a s.b
def Valid (y : ℕ) : Set ℕ → List St → Prop
  | W, [] => y ∈ W
  | W, s :: l => s.a ∈ W ∧ s.b ∈ W ∧ s.val ∉ W ∧ Valid y (insert s.val W) l
def need (y : ℕ) : List St → Finset ℕ
  | [] => {y}
  | s :: l => insert s.a (insert s.b ((need y l).erase s.val))
def Useful (y : ℕ) : List St → Prop
  | [] => True
  | s :: l => s.val ∈ need y l ∧ Useful y l
def killB (m : ℕ) (s : St) : Bool := Nat.beq (Nat.land s.a m) 0 || Nat.beq (Nat.land s.b m) 0
def kills (m : ℕ) (l : List St) : ℕ := l.countP (killB m)
def Chain : ℕ → List St → Prop
  | _, [] => True
  | p, s :: l => (s.a = p ∨ s.b = p ∨ p ≤ s.val) ∧ Chain s.val l
lemma valid_of_der {k : ℕ} {W : Set ℕ} {y : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l := by
  induction h with
  | here hy => exact ⟨[], by simp, hy⟩
  | weak _ ih => obtain ⟨l, h1, h2⟩ := ih; exact ⟨l, by omega, h2⟩
  | @step k W y t a b ha hb _ ih =>
    obtain ⟨l, h1, h2⟩ := ih
    by_cases hc : opN t a b ∈ W
    · rw [Set.insert_eq_of_mem hc] at h2; exact ⟨l, by omega, h2⟩
    · exact ⟨⟨t, a, b⟩ :: l, by simp; omega, ha, hb, hc, h2⟩
lemma need_sub {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → ∀ x ∈ need y l, x ∈ W := by
  induction l with
  | nil => intro W h x hx; rw [need, Finset.mem_singleton] at hx; rw [hx]; exact h
  | cons s l ih =>
    intro W h x hx
    obtain ⟨ha, hb, hc, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨h1, h2⟩
    · exact ha
    · exact hb
    · exact (ih hv x h2).resolve_left h1
lemma valid_drop {y c : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y (insert c W) l →
    c ∉ need y l → Valid y W l := by
  induction l with
  | nil =>
    intro W h hc
    rw [need, Finset.mem_singleton] at hc
    exact h.resolve_left (fun e => hc e.symm)
  | cons s l ih =>
    intro W h hc
    obtain ⟨ha, hb, hf, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have hne : c ≠ s.val := fun e => hf (Or.inl e.symm)
    refine ⟨ha.resolve_left (Ne.symm h1), hb.resolve_left (Ne.symm h2), fun h => hf (Or.inr h), ?_⟩
    rw [Set.insert_comm] at hv
    exact ih hv (h3 hne)
lemma useful_of_min {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l →
    (∀ l', Valid y W l' → l.length ≤ l'.length) → Useful y l := by
  induction l with
  | nil => intro W _ _; trivial
  | cons s l ih =>
    intro W h hmin
    obtain ⟨ha, hb, hf, hv⟩ := h
    refine ⟨?_, ih hv fun l' hl' => ?_⟩
    · by_contra hc
      have := hmin l (valid_drop l hv hc)
      simp at this
    · have := hmin (s :: l') ⟨ha, hb, hf, hl'⟩
      simpa using this
lemma need_card {y : ℕ} (l : List St) (h : Useful y l) : (need y l).card ≤ l.length + 1 := by
  induction l with
  | nil => simp [need]
  | cons s l ih =>
    obtain ⟨h1, h2⟩ := h
    have e := Finset.card_erase_of_mem h1
    have i := ih h2
    have c1 := Finset.card_insert_le s.a (insert s.b ((need y l).erase s.val))
    have c2 := Finset.card_insert_le s.b ((need y l).erase s.val)
    have p := Finset.card_pos.mpr ⟨_, h1⟩
    rw [need, List.length_cons]
    omega
lemma need_next {y : ℕ} {s : St} {l : List St} {x : ℕ} (h : x ∈ need y l) :
    x = s.val ∨ x ∈ need y (s :: l) := by
  by_cases hx : x = s.val
  · exact Or.inl hx
  · right; rw [need]; simp [hx, h]
lemma need_agree {y i j : ℕ} (l : List St) (h : ∀ x ∈ need y l, x.testBit i = x.testBit j) :
    y.testBit i = y.testBit j := by
  induction l with
  | nil => exact h y (by simp [need])
  | cons s l ih =>
    refine ih fun x hx => ?_
    rcases need_next (s := s) hx with rfl | hx
    · rw [St.val, opN_bit, opN_bit, h s.a (by simp [need]), h s.b (by simp [need])]
    · exact h x hx
lemma kill_forced {y m x : ℕ} (hy : Nat.land y m ≠ 0) (l : List St) (hx : x ∈ need y l)
    (hm : Nat.land x m = 0) : 1 ≤ kills m l := by
  induction l with
  | nil => rw [need, Finset.mem_singleton] at hx; rw [hx] at hm; exact absurd hm hy
  | cons s l ih =>
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    have hk : killB m s = true → 1 ≤ kills m (s :: l) := fun h => by
      rw [kills, List.countP_cons_of_pos h]; omega
    rcases hx with rfl | rfl | ⟨_, h2⟩
    · exact hk (by unfold killB; rw [hm]; rfl)
    · exact hk (by unfold killB; rw [hm]; exact Bool.or_true _)
    · have := ih h2
      have c : kills m l ≤ kills m (s :: l) := by
        rw [kills, kills, List.countP_cons]; omega
      omega
lemma land_op (t : Fin 4) (a b m : ℕ) :
    Nat.land (opN t a b) m = opN t (Nat.land a m) (Nat.land b m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [land_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> cases m.testBit i <;> rfl
lemma opN_zero_left (t : Fin 4) (b : ℕ) : opN t 0 b = 0 ∨ opN t 0 b = b := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t 0 b).testBit i = c (b.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t 0 b = 0 ∨ opN t 0 b = b := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key _ (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
def swapT : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2
lemma opN_swap (t : Fin 4) (a b : ℕ) : opN t a b = opN (swapT t) b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [opN_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> rfl
lemma opN_zero_right (t : Fin 4) (b : ℕ) : opN t b 0 = 0 ∨ opN t b 0 = b := by
  rw [opN_swap]; exact opN_zero_left _ _
lemma opN_self (t : Fin 4) (a : ℕ) : opN t a a = 0 ∨ opN t a a = a := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t a a).testBit i = c (a.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t a a = 0 ∨ opN t a a = a := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
lemma der_masked {y m : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → 0 ∈ W →
    ∃ n, n + kills m l = l.length ∧ Der opN n ((fun w => Nat.land w m) '' W) (Nat.land y m) := by
  induction l with
  | nil => intro W h _; exact ⟨0, by simp [kills], Der.here ⟨y, h, rfl⟩⟩
  | cons s l ih =>
    intro W h h0
    obtain ⟨ha, hb, _, hv⟩ := h
    obtain ⟨n, hn, hd⟩ := ih hv (Or.inr h0)
    have im (w : ℕ) (hw : w ∈ W) : Nat.land w m ∈ (fun w => Nat.land w m) '' W := ⟨w, hw, rfl⟩
    have z : 0 ∈ (fun w => Nat.land w m) '' W := ⟨0, h0, by simp [Nat.land]⟩
    by_cases hk : killB m s = true
    · refine ⟨n, ?_, hd.mono ?_⟩
      · rw [kills, List.countP_cons_of_pos hk, List.length_cons]
        rw [kills] at hn; omega
      · rintro _ ⟨w, rfl | hw, rfl⟩
        · show Nat.land s.val m ∈ _
          rw [St.val, land_op]
          rw [killB, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at hk
          rcases hk with h | h
          · rw [h]
            rcases opN_zero_left s.t (Nat.land s.b m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ hb
          · rw [h]
            rcases opN_zero_right s.t (Nat.land s.a m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ ha
        · exact im w hw
    · refine ⟨n + 1, ?_, ?_⟩
      · rw [kills, List.countP_cons_of_neg hk, List.length_cons]
        rw [kills] at hn; omega
      · refine Der.step s.t _ _ (im _ ha) (im _ hb) ?_
        rw [Set.image_insert_eq] at hd
        have e : Nat.land s.val m = opN s.t (Nat.land s.a m) (Nat.land s.b m) := land_op _ _ _ _
        rw [← e]; exact hd
lemma valid_swap {y : ℕ} (s1 s2 : St) (post : List St) (h1 : s2.a ≠ s1.val) (h2 : s2.b ≠ s1.val)
    (pre : List St) : ∀ {W : Set ℕ}, Valid y W (pre ++ s1 :: s2 :: post) →
      Valid y W (pre ++ s2 :: s1 :: post) := by
  induction pre with
  | nil =>
    intro W h
    obtain ⟨ha, hb, hc, ha2, hb2, hc2, hv⟩ := h
    refine ⟨ha2.resolve_left h1, hb2.resolve_left h2, fun h => hc2 (Or.inr h), Or.inr ha, Or.inr hb,
      ?_, ?_⟩
    · rintro (e | h)
      · exact hc2 (Or.inl e.symm)
      · exact hc h
    · rw [Set.insert_comm]; exact hv
  | cons s pre ih =>
    intro W h
    obtain ⟨ha, hb, hc, hv⟩ := h
    exact ⟨ha, hb, hc, ih hv⟩
def keyN (l : List St) : ℕ := l.foldl (fun acc s => 2 * acc + s.val) 0
lemma fold_lt (l : List St) : ∀ {x x' : ℕ}, x < x' →
    l.foldl (fun acc s => 2 * acc + s.val) x < l.foldl (fun acc s => 2 * acc + s.val) x' := by
  induction l with
  | nil => intro x x' h; exact h
  | cons s l ih =>
    intro x x' h
    exact ih (show 2 * x + s.val < 2 * x' + s.val by omega)
lemma key_swap (pre post : List St) (s1 s2 : St) (h : s2.val < s1.val) :
    keyN (pre ++ s2 :: s1 :: post) < keyN (pre ++ s1 :: s2 :: post) := by
  unfold keyN
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_cons]
  exact fold_lt post (by omega)
lemma chain_of {l : List St} : ∀ (p : ℕ),
    (∀ s l', l = s :: l' → (s.a = p ∨ s.b = p ∨ p ≤ s.val)) →
    (∀ pre s1 s2 post, l = pre ++ s1 :: s2 :: post →
      (s2.a = s1.val ∨ s2.b = s1.val ∨ s1.val ≤ s2.val)) → Chain p l := by
  induction l with
  | nil => intro p _ _; trivial
  | cons s l ih =>
    intro p h1 h2
    refine ⟨h1 s l rfl, ih s.val (fun s' l' e => ?_) (fun pre s1 s2 post e => ?_)⟩
    · exact h2 [] s s' l' (by rw [e]; rfl)
    · exact h2 (s :: pre) s1 s2 post (by rw [e]; rfl)
lemma exists_min {α : Type} (S : Set α) (f : α → ℕ) (h : S.Nonempty) :
    ∃ l ∈ S, ∀ l' ∈ S, f l ≤ f l' := by
  obtain ⟨l, hl, hm⟩ := (measure f).wf.has_min S h
  exact ⟨l, hl, fun l' hl' => not_lt.mp (hm l' hl')⟩
def headV : List St → ℕ
  | [] => 0
  | s :: _ => s.val
lemma exists_sorted {y : ℕ} {W : Set ℕ} {k : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l ∧ Useful y l ∧ Chain 0 l ∧
      ∀ l', Valid y W l' → l'.length = l.length → headV l ≤ headV l' := by
  obtain ⟨l0, hk0, hv0⟩ := valid_of_der h
  obtain ⟨l1, hv1, hmin⟩ := exists_min {l | Valid y W l} List.length ⟨l0, hv0⟩
  obtain ⟨l2, ⟨hv2, hlen2⟩, hhead⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length} headV ⟨l1, hv1, rfl⟩
  obtain ⟨l, ⟨hv, hlen, hh⟩, hkey⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length ∧ headV l = headV l2} keyN ⟨l2, hv2, hlen2, rfl⟩
  refine ⟨l, ?_, hv, useful_of_min l hv (fun l' hl' => by rw [hlen]; exact hmin l' hl'), ?_, ?_⟩
  · rw [hlen]; exact (hmin l0 hv0).trans hk0
  · refine chain_of 0 (fun s l' _ => Or.inr (Or.inr (Nat.zero_le _))) ?_
    intro pre s1 s2 post e
    by_contra hc
    push Not at hc
    obtain ⟨c1, c2, c3⟩ := hc
    rw [e] at hv hlen hh hkey
    have sv := valid_swap s1 s2 post c1 c2 pre hv
    have sl : (pre ++ s2 :: s1 :: post).length = l1.length := by
      rw [← hlen]; simp
    cases pre with
    | nil =>
      have := hhead _ ⟨sv, sl⟩
      rw [← hh] at this
      change s1.val ≤ s2.val at this
      omega
    | cons p pre =>
      have := hkey _ ⟨sv, sl, by rw [← hh]; rfl⟩
      have := key_swap (p :: pre) post s1 s2 c3
      omega
  · intro l' hl' hl
    rw [hh]; exact hhead l' ⟨hl', by rw [hl, hlen]⟩
lemma step_facts {y : ℕ} {W : Set ℕ} {s : St} {l : List St} (h : Valid y W (s :: l)) (h0 : 0 ∈ W) :
    s.a ≠ 0 ∧ s.b ≠ 0 ∧ s.a ≠ s.b ∧ s.val ≠ 0 ∧ s.val ≠ s.a ∧ s.val ≠ s.b ∧
      s.val ∉ need y (s :: l) := by
  have hn := need_sub (s :: l) h
  obtain ⟨ha, hb, hc, _⟩ := h
  refine ⟨?_, ?_, ?_, fun e => hc (e ▸ h0), fun e => hc (e ▸ ha), fun e => hc (e ▸ hb),
    fun hh => hc (hn _ hh)⟩
  · intro e
    rcases opN_zero_left s.t s.b with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact hb)
  · intro e
    rcases opN_zero_right s.t s.a with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact ha)
  · intro e
    rcases opN_self s.t s.a with h | h
    · exact hc (by rw [St.val, ← e, h]; exact h0)
    · exact hc (by rw [St.val, ← e, h]; exact ha)
structure Wr where
  w : ℕ
  s : ℕ
  f : ℕ
def sepN (L w : ℕ) : ℕ := Nat.land (Nat.xor w (Nat.shiftRight w 143)) L
def covL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.s (covL l)
def flL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.f (flL l)
def lenL : List Wr → ℕ
  | [] => 0
  | _ :: l => Nat.succ (lenL l)
def absentL (g : ℕ) : List Wr → Bool
  | [] => true
  | x :: l => cond (Nat.beq x.w g) false (absentL g l)
def app : List Wr → List Wr → List Wr
  | [], m => m
  | a :: l, m => a :: app l m
def sub (a b : ℕ) : Bool := Nat.beq (Nat.land a b) a
def force (x : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun n _ => f (Nat.succ n)) x
lemma force_eq (x : ℕ) (f : ℕ → Bool) : force x f = f x := by cases x <;> rfl
abbrev Next := List Wr → ℕ → ℕ → ℕ → ℕ → Bool
def tryG (L : ℕ) (r : Next) (k m : ℕ) (rest : List Wr) (cr c1 c2 c3 : ℕ) (a b : Wr) (last : ℕ)
    (uses : Bool) (g fg : ℕ) : Bool :=
  cond (Nat.beq g 0) false (cond (Nat.beq g a.w) false (cond (Nat.beq g b.w) false
    (cond (cond uses true (Nat.ble last g))
      (cond (sub fg c1)
        (force (sepN L g) fun sg =>
          force (Nat.lor cr sg) fun base =>
            (cond (Nat.beq base L) (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: rest) c1 c2 c3 g) false)
              false) ||
            (cond (Nat.ble m (Nat.succ k))
              ((cond (sub a.f c1) (cond (Nat.beq (Nat.lor base a.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (sub b.f c1) (cond (Nat.beq (Nat.lor base b.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: b :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (Nat.ble m k) (cond (sub a.f c1) (cond (sub b.f c1)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: b :: rest) c1 c2 c3 g) false) false)
                  false) false))
              false))
        false)
      false)))
def tryP (L : ℕ) (r : Next) (k m c1 c2 c3 last : ℕ) (a b : Wr) (rest : List Wr) : Bool :=
  force (Nat.lor a.f b.f) fun K =>
    cond (sub K c1)
      (force (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K))) fun d1 =>
       force (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) fun d2 =>
       force (Nat.xor c3 (Nat.land c3 K)) fun d3 =>
        cond (sub (flL rest) d1)
          (force (covL rest) fun cr =>
            force (Nat.land a.w b.w) fun ab =>
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last) ab K ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.lor a.w b.w) (Nat.land a.f b.f) ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor a.w ab) a.f ||
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor b.w ab) b.f)))
          false)
      false
def pairsB (a : Wr) : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, b :: l => (a, b, app acc l) :: pairsB a (b :: acc) l
def pairsA : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, a :: l => pairsB a acc l ++ pairsA (a :: acc) l
def anyP (p : Wr → Wr → List Wr → Bool) : List (Wr × Wr × List Wr) → Bool
  | [] => false
  | x :: l => p x.1 x.2.1 x.2.2 || anyP p l
def isT (y : ℕ) : List Wr → Bool
  | [a] => Nat.beq a.w y
  | _ => false
def search (L y : ℕ) : ℕ → Next
  | 0, v, _, _, _, _ => isT y v
  | k + 1, v, c1, c2, c3, last =>
    isT y v || anyP (tryP L (search L y k) k (lenL v) c1 c2 c3 last) (pairsA [] v)
lemma lenL_eq (v : List Wr) : lenL v = v.length := by
  induction v with
  | nil => rfl
  | cons a l ih => rw [lenL, ih]; rfl
lemma app_eq (a b : List Wr) : app a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x l ih => rw [app, ih]; rfl
lemma absent_true {g : ℕ} {l : List Wr} (h : ∀ x ∈ l, x.w ≠ g) : absentL g l = true := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : Nat.beq x.w g = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]; exact h x (by simp)
    rw [absentL, hx]
    exact ih fun u hu => h u (by simp [hu])
lemma sub_true {a b : ℕ} (h : ∀ i, a.testBit i = true → b.testBit i = true) : sub a b = true := by
  rw [sub, Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [land_bit]
  cases ha : a.testBit i
  · rfl
  · rw [h i ha]; rfl
lemma anyP_true {p : Wr → Wr → List Wr → Bool} {l : List (Wr × Wr × List Wr)} {a b : Wr}
    {r : List Wr} (hm : (a, b, r) ∈ l) (hp : p a b r = true) : anyP p l = true := by
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    rw [anyP, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with rfl | h
    · exact Or.inl hp
    · exact Or.inr (ih h)
lemma pairsB_spec (a b : Wr) (l : List Wr) : ∀ acc : List Wr, b ∈ l →
    ∃ r, (a, b, r) ∈ pairsB a acc l ∧ (acc ++ l).Perm (b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨acc ++ l, by simp [pairsB, app_eq], List.perm_middle⟩
    · obtain ⟨r, h1, h2⟩ := ih (x :: acc) h
      exact ⟨r, by simp [pairsB, h1], List.perm_middle.trans h2⟩
lemma pairsA_spec (a b : Wr) (hab : a ≠ b) (l : List Wr) : ∀ acc : List Wr, a ∈ l → b ∈ l →
    ∃ r, ((a, b, r) ∈ pairsA acc l ∨ (b, a, r) ∈ pairsA acc l) ∧ (acc ++ l).Perm (a :: b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc ha hb
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with e | hb'
      · exact absurd e.symm hab
      · obtain ⟨r, h1, h2⟩ := pairsB_spec a b l acc hb'
        exact ⟨r, Or.inl (by rw [pairsA]; exact List.mem_append_left _ h1),
          List.perm_middle.trans (h2.cons a)⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, h1, h2⟩ := pairsB_spec b a l acc ha'
        exact ⟨r, Or.inr (by rw [pairsA]; exact List.mem_append_left _ h1),
          (List.perm_middle.trans (h2.cons b)).trans (List.Perm.swap a b r)⟩
      · obtain ⟨r, h1, h2⟩ := ih (x :: acc) ha' hb'
        refine ⟨r, ?_, List.perm_middle.trans h2⟩
        rcases h1 with h | h
        · exact Or.inl (by rw [pairsA]; exact List.mem_append_right _ h)
        · exact Or.inr (by rw [pairsA]; exact List.mem_append_right _ h)
structure Rep (L H : ℕ) (mask : ℕ → ℕ) (v : List Wr) (S : Finset ℕ) : Prop where
  nd : (v.map Wr.w).Nodup
  mem : ∀ x, x ∈ S ↔ ∃ u ∈ v, u.w = x
  sep : ∀ u ∈ v, u.s = sepN L u.w
  fl : ∀ u ∈ v, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0
def Bud (H : ℕ) (mask : ℕ → ℕ) (c1 c2 c3 : ℕ) (l : List St) : Prop :=
  ∀ h < H, kills (mask h) l ≤ 3 ∧ (1 ≤ kills (mask h) l → c1.testBit h = true) ∧
    (2 ≤ kills (mask h) l → c2.testBit h = true) ∧ (3 ≤ kills (mask h) l → c3.testBit h = true)
lemma cov_bit (l : List Wr) (i : ℕ) : (covL l).testBit i = l.any fun a => a.s.testBit i := by
  induction l with
  | nil => simp [covL]
  | cons a l ih => rw [covL, lor_bit, ih, List.any_cons]
lemma fl_bit (l : List Wr) (i : ℕ) : (flL l).testBit i = l.any fun a => a.f.testBit i := by
  induction l with
  | nil => simp [flL]
  | cons a l ih => rw [flL, lor_bit, ih, List.any_cons]
lemma sepN_bit (L w i : ℕ) :
    (sepN L w).testBit i = ((w.testBit i != w.testBit (143 + i)) && L.testBit i) := by
  rw [sepN, land_bit, xor_bit, shr_bit]
lemma rep_cov {L H y : ℕ} {mask : ℕ → ℕ}
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) {v : List Wr} {l : List St}
    (hr : Rep L H mask v (need y l)) : covL v = L := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [cov_bit]
  cases hi : L.testBit i
  · rw [List.any_eq_false]
    intro u hu
    rw [hr.sep u hu, sepN_bit, hi]; simp
  · rw [List.any_eq_true]
    by_contra hc
    push Not at hc
    refine hL i hi (need_agree l fun x hx => ?_)
    obtain ⟨u, hu, rfl⟩ := (hr.mem x).mp hx
    have := hc u hu
    rw [hr.sep u hu, sepN_bit, hi] at this
    cases h1 : u.w.testBit i <;> cases h2 : u.w.testBit (143 + i) <;> simp_all
lemma rep_len {L H : ℕ} {mask : ℕ → ℕ} {v : List Wr} {S : Finset ℕ} (hr : Rep L H mask v S) :
    v.length = S.card := by
  have e : S = (v.map Wr.w).toFinset := by
    ext x; rw [hr.mem, List.mem_toFinset, List.mem_map]
  rw [e, List.toFinset_card_of_nodup hr.nd, List.length_map]
lemma flag_forced {H y : ℕ} {mask : ℕ → ℕ} (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    {l : List St} {d1 d2 d3 : ℕ} (hb : Bud H mask d1 d2 d3 l) {f x : ℕ} (hx : x ∈ need y l)
    (hf : ∀ h, f.testBit h = true → h < H ∧ Nat.land x (mask h) = 0) : sub f d1 = true := by
  refine sub_true fun h hh => ?_
  obtain ⟨h1, h2⟩ := hf h hh
  exact (hb h h1).2.1 (kill_forced (hy h h1) l hx h2)
lemma tryG_true {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {v rest : List Wr} {a b : Wr} {l : List St} {g fg last d1 d2 d3 m : ℕ} {uses : Bool}
    (hm : m = v.length) (hv : Rep L H mask v (insert a.w (insert b.w ((need y l).erase g))))
    (hp : v.Perm (a :: b :: rest)) (hg : g ∈ need y l) (hg0 : g ≠ 0) (hab : a.w ≠ b.w)
    (hgS : g ∉ insert a.w (insert b.w ((need y l).erase g)))
    (hfg : ∀ h, fg.testBit h = true → h < H ∧ Nat.land g (mask h) = 0)
    (hcard : (need y l).card ≤ k + 1) (hord : uses = true ∨ last ≤ g)
    (hb : Bud H mask d1 d2 d3 l)
    (hr : ∀ v', Rep L H mask v' (need y l) → r v' d1 d2 d3 g = true) :
    tryG L r k m rest (covL rest) d1 d2 d3 a b last uses g fg = true := by
  have hga : g ≠ a.w := fun e => hgS (by simp [e])
  have hgb : g ≠ b.w := fun e => hgS (by simp [e])
  have nd2 : ((a :: b :: rest).map Wr.w).Nodup := (hp.map Wr.w).nodup_iff.mp hv.nd
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at nd2
  obtain ⟨⟨_, har⟩, hbr, hrr⟩ := nd2
  have memr (x : ℕ) : x ∈ rest.map Wr.w ↔ x ∈ need y l ∧ x ≠ g ∧ x ≠ a.w ∧ x ≠ b.w := by
    have h1 : (x ∈ insert a.w (insert b.w ((need y l).erase g))) ↔ ∃ u ∈ a :: b :: rest, u.w = x := by
      rw [hv.mem]; exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hp.mem_iff.mp hu, e⟩, fun ⟨u, hu, e⟩ => ⟨u, hp.mem_iff.mpr hu, e⟩⟩
    rw [List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h2 := h1.mpr ⟨u, by simp [hu], rfl⟩
      have n1 : u.w ≠ a.w := fun e => har (e ▸ List.mem_map_of_mem hu)
      have n2 : u.w ≠ b.w := fun e => hbr (e ▸ List.mem_map_of_mem hu)
      simp only [Finset.mem_insert, Finset.mem_erase] at h2
      rcases h2 with h | h | ⟨h3, h4⟩
      · exact absurd h n1
      · exact absurd h n2
      · exact ⟨h4, h3, n1, n2⟩
    · rintro ⟨h2, h3, h4, h5⟩
      obtain ⟨u, hu, e⟩ := h1.mp (by simp [h2, h3])
      simp only [List.mem_cons] at hu
      rcases hu with rfl | rfl | hu
      · exact absurd e.symm h4
      · exact absurd e.symm h5
      · exact ⟨u, hu, e⟩
  have hgr : g ∉ rest.map Wr.w := fun h => ((memr g).mp h).2.1 rfl
  have sepr : ∀ u ∈ rest, u.s = sepN L u.w := fun u hu => hv.sep u (hp.mem_iff.mpr (by simp [hu]))
  have flr : ∀ u ∈ rest, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0 :=
    fun u hu => hv.fl u (hp.mem_iff.mpr (by simp [hu]))
  have sepa := hv.sep a (hp.mem_iff.mpr (by simp))
  have sepb := hv.sep b (hp.mem_iff.mpr (by simp))
  have fla := hv.fl a (hp.mem_iff.mpr (by simp))
  have flb := hv.fl b (hp.mem_iff.mpr (by simp))
  have len : v.length = rest.length + 2 := by rw [hp.length_eq]; simp
  have b1 : Nat.beq g 0 = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hg0
  have b2 : Nat.beq g a.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hga
  have b3 : Nat.beq g b.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hgb
  have b4 : (cond uses true (Nat.ble last g)) = true := by
    rcases hord with h | h
    · rw [h]; rfl
    · cases uses
      · exact Nat.ble_eq.mpr h
      · rfl
  have b5 : sub fg d1 = true := flag_forced hy hb hg hfg
  have b6 : absentL g rest = true :=
    absent_true fun x hx e => hgr (e ▸ List.mem_map_of_mem hx)
  set G : Wr := ⟨g, sepN L g, fg⟩ with hG
  unfold tryG
  rw [b1, b2, b3, b4, b5, force_eq, force_eq, b6]
  simp only [cond_false, cond_true]
  by_cases hA : a.w ∈ need y l <;> by_cases hB : b.w ∈ need y l
  · have R : Rep L H mask (G :: a :: b :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hga, hgb, hgr⟩, ⟨hab, har⟩, hbr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact ⟨a, by simp, e2.symm⟩
          by_cases e3 : x = b.w
          · exact ⟨b, by simp, e3.symm⟩
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | rfl | hu
          · exact hg
          · exact hA
          · exact hB
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | rfl | hu
        · rfl
        · exact sepa
        · exact sepb
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | rfl | hu
        · exact hfg
        · exact fla
        · exact flb
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have c2 : Nat.ble m k = true := by rw [Nat.ble_eq]; omega
    rw [c1, c2, flag_forced hy hb hA fla, flag_forced hy hb hB flb, hr _ R]
    simp
  · have R : Rep L H mask (G :: a :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hga, hgr⟩, har, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact ⟨a, by simp, e2.symm⟩
          by_cases e3 : x = b.w
          · exact absurd (e3 ▸ hx) hB
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | hu
          · exact hg
          · exact hA
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · rfl
        · exact sepa
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · exact hfg
        · exact fla
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have cv : Nat.beq (Nat.lor (Nat.lor (covL rest) (sepN L g)) a.s) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> cases a.s.testBit i <;> rfl
    rw [c1, flag_forced hy hb hA fla, cv, hr _ R]
    simp
  · have R : Rep L H mask (G :: b :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hgb, hgr⟩, hbr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact absurd (e2 ▸ hx) hA
          by_cases e3 : x = b.w
          · exact ⟨b, by simp, e3.symm⟩
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | hu
          · exact hg
          · exact hB
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · rfl
        · exact sepb
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · exact hfg
        · exact flb
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have cv : Nat.beq (Nat.lor (Nat.lor (covL rest) (sepN L g)) b.s) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> cases b.s.testBit i <;> rfl
    rw [c1, flag_forced hy hb hB flb, cv, hr _ R]
    simp
  · have R : Rep L H mask (G :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨hgr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact absurd (e2 ▸ hx) hA
          by_cases e3 : x = b.w
          · exact absurd (e3 ▸ hx) hB
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact hg
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · rfl
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact hfg
        · exact flr u hu
    have cv : Nat.beq (Nat.lor (covL rest) (sepN L g)) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> rfl
    rw [cv, hr _ R]
    simp
lemma kills_cons (m : ℕ) (s : St) (l : List St) :
    kills m (s :: l) = kills m l + if killB m s = true then 1 else 0 := by
  rw [kills, kills, List.countP_cons]
lemma bud_next {H c1 c2 c3 K : ℕ} {mask : ℕ → ℕ} {s : St} {l : List St}
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hK : ∀ h, K.testBit h = true → h < H ∧ killB (mask h) s = true) :
    sub K c1 = true ∧ Bud H mask (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K)))
      (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) (Nat.xor c3 (Nat.land c3 K)) l := by
  constructor
  · refine sub_true fun h hh => ?_
    obtain ⟨h1, h2⟩ := hK h hh
    refine (hb h h1).2.1 ?_
    rw [kills_cons, if_pos h2]; omega
  · intro h hh
    obtain ⟨b0, b1, b2, b3⟩ := hb h hh
    rw [kills_cons] at b0 b1 b2 b3
    simp only [lor_bit, xor_bit, land_bit]
    cases hk : K.testBit h
    · refine ⟨by split_ifs at b0 <;> omega, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
      · rw [b1 (by omega)]; simp
      · rw [b2 (by omega)]; simp
      · rw [b3 (by omega)]; simp
    · rw [if_pos (hK h hk).2] at b0 b1 b2 b3
      refine ⟨by omega, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
      · rw [b2 (by omega)]; simp
      · rw [b3 (by omega)]; simp
      · omega
lemma tryP_true {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {v rest : List Wr} {a b : Wr} {s : St} {l : List St} {last c1 c2 c3 m : ℕ} (t : Fin 4)
    (ht : opN t a.w b.w = s.val) (hm : m = v.length)
    (hv : Rep L H mask v (insert a.w (insert b.w ((need y l).erase s.val))))
    (hp : v.Perm (a :: b :: rest)) (hg : s.val ∈ need y l) (hg0 : s.val ≠ 0) (hab : a.w ≠ b.w)
    (hgS : s.val ∉ insert a.w (insert b.w ((need y l).erase s.val)))
    (hcard : (need y l).card ≤ k + 1) (hord : a.w = last ∨ b.w = last ∨ last ≤ s.val)
    (hkill : ∀ m, Nat.land a.w m = 0 ∨ Nat.land b.w m = 0 → killB m s = true)
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hr : ∀ v' d1 d2 d3, Rep L H mask v' (need y l) → Bud H mask d1 d2 d3 l →
      r v' d1 d2 d3 s.val = true) :
    tryP L r k m c1 c2 c3 last a b rest = true := by
  have fla := hv.fl a (hp.mem_iff.mpr (by simp))
  have flb := hv.fl b (hp.mem_iff.mpr (by simp))
  have hK : ∀ h, (Nat.lor a.f b.f).testBit h = true → h < H ∧ killB (mask h) s = true := by
    intro h hh
    rw [lor_bit, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨(fla h hh).1, hkill _ (Or.inl (fla h hh).2)⟩
    · exact ⟨(flb h hh).1, hkill _ (Or.inr (flb h hh).2)⟩
  obtain ⟨b1, hb'⟩ := bud_next hb hK
  have b2 : sub (flL rest) (Nat.lor c2 (Nat.xor c1 (Nat.land c1 (Nat.lor a.f b.f)))) = true := by
    refine sub_true fun h hh => ?_
    rw [fl_bit, List.any_eq_true] at hh
    obtain ⟨u, hu, hf⟩ := hh
    have uv := hp.mem_iff.mpr (show u ∈ a :: b :: rest by simp [hu])
    obtain ⟨h1, h2⟩ := hv.fl u uv h hf
    refine (hb' h h1).2.1 (kill_forced (hy h h1) l ?_ h2)
    have hS := (hv.mem u.w).mpr ⟨u, uv, rfl⟩
    have nd2 : ((a :: b :: rest).map Wr.w).Nodup := (hp.map Wr.w).nodup_iff.mp hv.nd
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at nd2
    obtain ⟨⟨_, har⟩, hbr, _⟩ := nd2
    simp only [Finset.mem_insert, Finset.mem_erase] at hS
    rcases hS with e | e | ⟨_, e⟩
    · exact absurd (e ▸ List.mem_map_of_mem hu) har
    · exact absurd (e ▸ List.mem_map_of_mem hu) hbr
    · exact e
  have hord' : (Nat.beq a.w last || Nat.beq b.w last) = true ∨ last ≤ s.val := by
    rcases hord with h | h | h
    · left; rw [h, Nat.beq_refl]; rfl
    · left; rw [h, Nat.beq_refl]; exact Bool.or_true _
    · exact Or.inr h
  have G (fg : ℕ) (hfg : ∀ h, fg.testBit h = true → h < H ∧ Nat.land s.val (mask h) = 0) :=
    tryG_true (m := m) (last := last) (uses := Nat.beq a.w last || Nat.beq b.w last) (fg := fg)
      hy hL hm hv hp hg hg0 hab hgS hfg hcard hord' hb' (fun v' hv' => hr v' _ _ _ hv' hb')
  have z (c x : ℕ) : Nat.land (opN t a.w b.w) c = opN t (Nat.land a.w c) (Nat.land b.w c) :=
    land_op t _ _ c
  unfold tryP
  rw [force_eq, b1]
  simp only [cond_true, force_eq]
  rw [b2]
  simp only [cond_true]
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
  fin_cases t
  · left
    have e : Nat.land a.w b.w = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [lor_bit, Bool.or_eq_true] at hh
    rw [← ht]
    refine ⟨(hK h (by rw [lor_bit, Bool.or_eq_true]; exact hh)).1, ?_⟩
    rw [z _ 0]
    rcases hh with hh | hh
    · rw [(fla h hh).2]
      rcases opN_zero_left 0 (Nat.land b.w (mask h)) with e | e
      · exact e
      · apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
    · rw [(flb h hh).2]
      apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; left
    have e : Nat.lor a.w b.w = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [land_bit, Bool.and_eq_true] at hh
    rw [← ht]
    refine ⟨(fla h hh.1).1, ?_⟩
    rw [z _ 0, (fla h hh.1).2, (flb h hh.2).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; right; left
    have e : Nat.xor a.w (Nat.land a.w b.w) = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [← ht]
    refine ⟨(fla h hh).1, ?_⟩
    rw [z _ 0, (fla h hh).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; right; right
    have e : Nat.xor b.w (Nat.land a.w b.w) = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [← ht]
    refine ⟨(flb h hh).1, ?_⟩
    rw [z _ 0, (flb h hh).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
lemma level {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {W : Set ℕ} {v : List Wr} {s : St} {l : List St} {last c1 c2 c3 : ℕ}
    (hV : Valid y W (s :: l)) (h0 : 0 ∈ W) (hU : Useful y (s :: l)) (hk : (s :: l).length ≤ k + 1)
    (hC : Chain last (s :: l)) (hv : Rep L H mask v (need y (s :: l)))
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hr : ∀ v' d1 d2 d3, Rep L H mask v' (need y l) → Bud H mask d1 d2 d3 l →
      r v' d1 d2 d3 s.val = true) :
    anyP (tryP L r k (lenL v) c1 c2 c3 last) (pairsA [] v) = true := by
  obtain ⟨fa, fb, fab, fv, _, _, fS⟩ := step_facts hV h0
  obtain ⟨ua, hua, ea⟩ := (hv.mem s.a).mp (by simp [need])
  obtain ⟨ub, hub, eb⟩ := (hv.mem s.b).mp (by simp [need])
  have hne : ua ≠ ub := fun e => fab (by rw [← ea, ← eb, e])
  obtain ⟨rest, hmem, hperm⟩ := pairsA_spec ua ub hne v [] hua hub
  have hcard : (need y l).card ≤ k + 1 := by
    have := need_card l hU.2
    simp only [List.length_cons] at hk
    omega
  have hg := hU.1
  have eN : need y (s :: l) = insert s.a (insert s.b ((need y l).erase s.val)) := rfl
  rcases hmem with hm | hm
  · refine anyP_true hm (tryP_true hy hL s.t (by rw [ea, eb]; rfl) (lenL_eq v) ?_ hperm hg fv
      (by rw [ea, eb]; exact fab) ?_ hcard ?_ ?_ hb hr)
    · rw [ea, eb]; exact hv
    · rw [ea, eb]; exact fS
    · rw [ea, eb]; exact hC.1
    · intro m h
      rw [ea, eb] at h
      unfold killB
      rcases h with h | h
      · rw [h]; rfl
      · rw [h]; exact Bool.or_true _
  · have hv2 : Rep L H mask v (insert ub.w (insert ua.w ((need y l).erase s.val))) := by
      rw [ea, eb, Finset.insert_comm]; exact hv
    refine anyP_true hm (tryP_true hy hL (swapT s.t) ?_ (lenL_eq v) hv2
      (hperm.trans (List.Perm.swap ub ua rest)) hg fv (by rw [ea, eb]; exact fab.symm) ?_ hcard ?_ ?_
      hb hr)
    · rw [ea, eb, ← opN_swap]; rfl
    · rw [ea, eb, Finset.insert_comm]; exact fS
    · rw [ea, eb]
      rcases hC.1 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · intro m h
      rw [ea, eb] at h
      unfold killB
      rcases h with h | h
      · rw [h]; exact Bool.or_true _
      · rw [h]; rfl
lemma isT_true {L H y : ℕ} {mask : ℕ → ℕ} {v : List Wr} (hv : Rep L H mask v (need y [])) :
    isT y v = true := by
  have hl := rep_len hv
  rw [need, Finset.card_singleton] at hl
  obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hl
  have : u.w ∈ need y [] := (hv.mem u.w).mpr ⟨u, by simp, rfl⟩
  rw [need, Finset.mem_singleton] at this
  rw [isT, this, Nat.beq_refl]
theorem search_complete {L H y : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) (k : ℕ) :
    ∀ (l : List St) (W : Set ℕ) (v : List Wr) (last c1 c2 c3 : ℕ), Valid y W l → 0 ∈ W →
      Useful y l → l.length ≤ k → Chain last l → Rep L H mask v (need y l) →
      Bud H mask c1 c2 c3 l → search L y k v c1 c2 c3 last = true := by
  induction k with
  | zero =>
    intro l W v last c1 c2 c3 hV h0 hU hk hC hv hb
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact isT_true hv
  | succ k ih =>
    intro l W v last c1 c2 c3 hV h0 hU hk hC hv hb
    rw [search, Bool.or_eq_true]
    cases l with
    | nil => exact Or.inl (isT_true hv)
    | cons s l =>
      refine Or.inr (level hy hL hV h0 hU hk hC hv hb fun v' d1 d2 d3 hv' hb' => ?_)
      exact ih l _ v' s.val d1 d2 d3 hV.2.2.2 (Or.inr h0) hU.2 (by simpa using hk) hC.2 hv' hb'
lemma need_ne_zero {y : ℕ} (hy : y ≠ 0) (l : List St) : ∀ {W : Set ℕ}, Valid y W l → 0 ∈ W →
    ∀ x ∈ need y l, x ≠ 0 := by
  induction l with
  | nil => intro W _ _ x hx; rw [need, Finset.mem_singleton] at hx; rw [hx]; exact hy
  | cons s l ih =>
    intro W h h0 x hx
    obtain ⟨fa, fb, _⟩ := step_facts h h0
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨_, h2⟩
    · exact fa
    · exact fb
    · exact ih h.2.2.2 (Or.inr h0) x h2
def neededB (L : ℕ) (ws : List Wr) : Bool :=
  ws.all fun u => !(Nat.beq (covL (ws.filter fun x => !(Nat.beq x.w u.w))) L)
lemma root_rep {L H y : ℕ} {mask : ℕ → ℕ}
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) (hy : y ≠ 0)
    {ws : List Wr} (hnd : (ws.map Wr.w).Nodup) (hs : ∀ u ∈ ws, u.s = sepN L u.w)
    (hf : ∀ u ∈ ws, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0)
    (hn : neededB L ws = true) {W : Set ℕ} {l : List St} (hV : Valid y W l) (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x) : Rep L H mask ws (need y l) := by
  have hsub : ∀ x ∈ need y l, ∃ u ∈ ws, u.w = x := fun x hx =>
    (hW x (need_sub l hV x hx)).resolve_left (need_ne_zero hy l hV h0 x hx)
  refine ⟨hnd, fun x => ⟨hsub x, ?_⟩, hs, hf⟩
  rintro ⟨u, hu, rfl⟩
  by_contra hc
  have hc1 := List.all_eq_true.mp hn u hu
  have hc2 : covL (ws.filter fun x => !(Nat.beq x.w u.w)) = L := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [cov_bit]
    cases hi : L.testBit i
    · rw [List.any_eq_false]
      intro q hq
      rw [hs q (List.mem_of_mem_filter hq), sepN_bit, hi]; simp
    · rw [List.any_eq_true]
      by_contra hd
      push Not at hd
      refine hL i hi (need_agree l fun x hx => ?_)
      obtain ⟨q, hq, rfl⟩ := hsub x hx
      have hne : q.w ≠ u.w := fun e => hc (e ▸ hx)
      have hq' : q ∈ ws.filter fun x => !(Nat.beq x.w u.w) := by
        rw [List.mem_filter]
        refine ⟨hq, ?_⟩
        have : Nat.beq q.w u.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hne
        rw [this]; rfl
      have := hd q hq'
      rw [hs q hq, sepN_bit, hi] at this
      cases h1 : q.w.testBit i <;> cases h2 : q.w.testBit (143 + i) <;> simp_all
  rw [hc2, Nat.beq_refl] at hc1
  exact Bool.false_ne_true hc1
theorem refute {L y K : ℕ} (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    (hy : y ≠ 0) {ws : List Wr} (hnd : (ws.map Wr.w).Nodup) (hs : ∀ u ∈ ws, u.s = sepN L u.w)
    (hf : ∀ u ∈ ws, u.f = 0) (hn : neededB L ws = true)
    (hsearch : search L y K ws 0 0 0 0 = false) {W : Set ℕ} (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x) : ¬ Der opN K W y := by
  intro h
  obtain ⟨l, hk, hV, hU, hC, _⟩ := exists_sorted h
  have hrep : Rep L 0 (fun _ => 0) ws (need y l) :=
    root_rep hL hy hnd hs (fun u hu h hh => by rw [hf u hu] at hh; simp at hh) hn hV h0 hW
  have := search_complete (H := 0) (mask := fun _ => 0) (fun h hh => by omega) hL K l W ws 0 0 0 0
    hV h0 hU hk hC hrep (fun h hh => by omega)
  rw [hsearch] at this
  exact Bool.false_ne_true this
lemma anyP_append (p : Wr → Wr → List Wr → Bool) (a b : List (Wr × Wr × List Wr)) :
    anyP p (a ++ b) = (anyP p a || anyP p b) := by
  induction a with
  | nil => rfl
  | cons x l ih => rw [List.cons_append, anyP, anyP, ih, Bool.or_assoc]
lemma anyP_chunks (p : Wr → Wr → List Wr → Bool) (m : ℕ) (n : ℕ) :
    ∀ l : List (Wr × Wr × List Wr), l.length ≤ m * n →
      (∀ i < n, anyP p ((l.drop (m * i)).take m) = false) → anyP p l = false := by
  induction n with
  | zero =>
    intro l hl _
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    rw [this]; rfl
  | succ n ih =>
    intro l hl h
    rw [← List.take_append_drop m l, anyP_append]
    have h1 := h 0 (by omega)
    rw [Nat.mul_zero, List.drop_zero] at h1
    rw [h1, Bool.false_or]
    refine ih _ (by rw [List.length_drop, Nat.mul_succ] at *; omega) fun i hi => ?_
    have := h (i + 1) (by omega)
    rw [List.drop_drop, show m + m * i = m * (i + 1) by ring]
    exact this
structure Kid where
  v : List Wr
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  g : ℕ
def eqL : List Wr → List Wr → Bool
  | [], [] => true
  | a :: l, b :: m => Nat.beq a.w b.w && (Nat.beq a.s b.s && (Nat.beq a.f b.f && eqL l m))
  | _, _ => false
lemma eqL_eq (a : List Wr) : ∀ b, eqL a b = true → a = b := by
  induction a with
  | nil => intro b h; cases b with
    | nil => rfl
    | cons => simp [eqL] at h
  | cons x l ih =>
    intro b h
    cases b with
    | nil => simp [eqL] at h
    | cons y m =>
      rw [eqL, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq,
        Nat.beq_eq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      rw [ih m h4]
      cases x; cases y
      simp only at h1 h2 h3
      rw [h1, h2, h3]
def isKid (v : List Wr) (c1 c2 c3 g : ℕ) : List Kid → Bool
  | [] => false
  | q :: l => (Nat.beq q.g g && (Nat.beq q.c1 c1 && (Nat.beq q.c2 c2 && (Nat.beq q.c3 c3 &&
      eqL q.v v)))) || isKid v c1 c2 c3 g l
lemma isKid_mem {v : List Wr} {c1 c2 c3 g : ℕ} (ks : List Kid)
    (h : isKid v c1 c2 c3 g ks = true) : ⟨v, c1, c2, c3, g⟩ ∈ ks := by
  induction ks with
  | nil => simp [isKid] at h
  | cons q l ih =>
    rw [isKid, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have := eqL_eq _ _ h5
      cases q
      simp only at h1 h2 h3 h4 this
      subst h1 h2 h3 h4 this
      simp
    · exact List.mem_cons_of_mem _ (ih h)
def memN (g : ℕ) : List ℕ → Bool
  | [] => false
  | x :: l => Nat.beq x g || memN g l
def rootNext (al : List ℕ) (ks : List Kid) : Next := fun v c1 c2 c3 g =>
  cond (memN g al) (!(isKid v c1 c2 c3 g ks)) false
def Bdd (N x : ℕ) : Prop := ∀ i, N ≤ i → x.testBit i = false
lemma bdd_op {N : ℕ} (t : Fin 4) {a b : ℕ} (ha : Bdd N a) (hb : Bdd N b) : Bdd N (opN t a b) := by
  intro i hi
  rw [opN_bit, ha i hi, hb i hi]
  fin_cases t <;> rfl
def sIdx (T : ℕ) (i : ℕ) : ℕ :=
  cond (Nat.blt i 143) (Nat.land (Nat.shiftRight T (8 * i)) 255)
    (143 + Nat.land (Nat.shiftRight T (8 * (i - 143))) 255)
def sg (N T : ℕ) (w : ℕ) : ℕ := Nat.ofBits fun i : Fin N => w.testBit (sIdx T i.val)
lemma sg_bit (N T w i : ℕ) (hi : i < N) : (sg N T w).testBit i = w.testBit (sIdx T i) := by
  rw [sg, Nat.testBit_ofBits_lt _ _ hi]
lemma sg_bdd (N T w : ℕ) : Bdd N (sg N T w) := fun i hi => by rw [sg, Nat.testBit_ofBits_ge _ _ hi]
lemma sg_op (N T : ℕ) (t : Fin 4) (a b : ℕ) : sg N T (opN t a b) = opN t (sg N T a) (sg N T b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, opN_bit, opN_bit, sg_bit _ _ _ _ hi, sg_bit _ _ _ _ hi]
  · rw [sg_bdd _ _ _ i (by omega), bdd_op t (sg_bdd N T a) (sg_bdd N T b) i (by omega)]
lemma sg_sg {N : ℕ} (T : ℕ) (hT : ∀ i < N, sIdx T i < N ∧ sIdx T (sIdx T i) = i) {w : ℕ} (hw : Bdd N w) :
    sg N T (sg N T w) = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, sg_bit _ _ _ _ (hT i hi).1, (hT i hi).2]
  · rw [sg_bdd _ _ _ i (by omega), hw i (by omega)]
def mapSt (N T : ℕ) (s : St) : St := ⟨s.t, sg N T s.a, sg N T s.b⟩
lemma mapSt_val (N T : ℕ) (s : St) : (mapSt N T s).val = sg N T s.val := (sg_op N T _ _ _).symm
lemma valid_map {N : ℕ} (T : ℕ) (hT : ∀ i < N, sIdx T i < N ∧ sIdx T (sIdx T i) = i) {y : ℕ}
    (l : List St) : ∀ {W : Set ℕ}, (∀ x ∈ W, Bdd N x) → Valid y W l →
      Valid (sg N T y) (sg N T '' W) (l.map (mapSt N T)) := by
  induction l with
  | nil => intro W _ h; exact ⟨y, h, rfl⟩
  | cons s l ih =>
    intro W hb h
    obtain ⟨ha, hb', hc, hv⟩ := h
    have bv : Bdd N s.val := bdd_op s.t (hb _ ha) (hb _ hb')
    refine ⟨⟨s.a, ha, rfl⟩, ⟨s.b, hb', rfl⟩, ?_, ?_⟩
    · rw [mapSt_val]
      rintro ⟨x, hx, e⟩
      have := congrArg (sg N T) e
      rw [sg_sg T hT (hb x hx), sg_sg T hT bv] at this
      exact hc (this ▸ hx)
    · rw [mapSt_val, ← Set.image_insert_eq]
      refine ih ?_ hv
      rintro x (rfl | hx)
      · exact bv
      · exact hb x hx
lemma sg_eq {N T x x' : ℕ} (hx' : Bdd N x') (h : ∀ i < N, x'.testBit i = x.testBit (sIdx T i)) :
    sg N T x = x' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, h i hi]
  · rw [sg_bdd _ _ _ i (by omega), hx' i (by omega)]
lemma bdd_of_lt {N x : ℕ} (h : x < 2 ^ N) : Bdd N x := fun i hi =>
  Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi))
def LO : ℕ := 0x7fffffffffffffffffffffffffffffffffff
def ipL : List ℕ := [0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f]
def ip (i : Fin 7) : ℕ := ipL.getD i.val 0
def maskL : List ℕ := [0x78f1e3c78f1e3c58a850404fffffffffffffffffffff01fc00000000000ffffffffffff, 0x39f3e7cf9f3e7cfa75ffffffad9022fffffffffffff80fe0000003ffffff000000ffffff, 0xe1c3870e1c38707fe005fffd26fff802ffffffffc07ffe03f8ffc001fff001fff000fff, 0x1ab56ad5ab56ad58fe2ff2bf87f0ffa5faaf80fe03ffffffffb1fc1fe03f0fe0ff03f00f, 0x3a74e9d3a74e9d3b7f7afbfb18f38f8e78faff01fffff01ffff6fce1e7c031e70f1cf1f0, 0x274e9d3a74e9d3af9fd33d63fb7fdd5a9d59fffe03f80fffffdf3f2678c7f6eb30253233, 0x35ebd7af5ebd7affa7ffadcdffbf71ffd7750001fc07ffffffff4fde1b1bff74c3d80cc0]
def mask (h : ℕ) : ℕ := maskL.getD h 0
def root : List Wr := [⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
def pm (p : Fin 3) (i : Fin 7) : Fin 7 :=
  match p with
  | 0 => ![3, 6, 2, 0, 5, 4, 1] i
  | 1 => ![4, 6, 2, 5, 0, 3, 1] i
  | 2 => ![5, 1, 2, 4, 3, 0, 6] i
def Tn (p : Fin 3) : ℕ :=
  match p with
  | 0 => 0x5d585a5b595c57726d6f706e716c6b666869676a65645f616260635e87828485838681807b7d7e7c7f7a797476777578738e898b8c8a8d884515123a3736082309212005044746494856171614132e2f2c2d3938533c3b5251240b0a2207063f403d3e110e0f10270c0d354f324d4c02031a1b1c1d00014443554241542b28292a252634334e5031304b4a1e1f1819
  | 1 => 0x6c6d6f706e717257585a5b595c5d7a7b7d7e7c7f805e5f616260636488898b8c8a8d8e65666869676a6b73747677757879818284858386871115103503023223091d1c0100434416172b484941422e2f292a3334240a0b1e1f533b3c5030313f400e0f453d3e12270c0d3a4f081a1b36374d4c2021040546475513142856542c2d252638394e220607181952514b4a
  | 2 => 0x81868584838287888d8c8b8a898e656a696867666b73787776757479575c5b5a59585d7a7f7e7d7c7b805e636261605f646c71706f6e6d722b5528241e1f224f4e1a1b1819161743441146471314403f0f0e0a0b35333403023a38390806072f2e2a29562d2c542726255323501d1c515221204c4d4a4b48491541421045123e3d0d0c3b3c09323031010037360504
def allowed : List ℕ := [0x3ffffc000000000000000000, 0x1fc07000000000ffe000000000, 0xfe00009031e183f000000000000, 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc]
def L0 : ℕ := 0xf1e3c78f003c00000000000ffffffffffff
def Y0 : ℕ := 0x7ffffffff01fc00000000000ffffffffffff
def ws0 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000007f01fc00000000000ffffff000000, 0xc1830603000c000000000005b2045000000, 0⟩, ⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060c603003000000000000a4c000005000, 0⟩, ⟨0x50a142850a1428500800400780f005a05507f01fc000000000000000000f01f00fc0ff0, 0x5141450a002800000000000000100480550, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xb082c58b002c00000000000000010000005, 0⟩, ⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x1023808e00040000000000000148a900880, 0⟩, ⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0xb1610584001000000000000000a2027a22a, 0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub0 : search L0 Y0 7 ws0 0 0 0 0 = false := by decide +kernel
def L1 : ℕ := 0x73e7cf980e60000003ffffff000000ffffff
def Y1 : ℕ := 0x7ffffff80fe0000003ffffff000000ffffff
def ws1 : List Wr := [⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe0000003ffffff000000000000, 0x70e1c38000600000010a0809000000000000, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f80000000003ffe000000000fff000, 0x63c78c800c6000000000a000000000005000, 0⟩, ⟨0x2142850a142850a201d00d402800005a05507f01fc000000000003e01fc0000000fc0ff0, 0x3184c6100840000000400540000000480550, 0⟩, ⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3e00c180e00000002141036000000000005, 0⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc000000000000d98738000000dacdcc, 0x316309880620000000800200000000900880, 0⟩, ⟨0x8102040810204005000523200000200288afffe03f8000000000021e4e400000027f33f, 0x63c64318020000000021408000000027a22a, 0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub1 : search L1 Y1 6 ws1 0 0 0 0 = false := by decide +kernel
def L2 : ℕ := 0x1c387001c3800e0ffc001fff001fff000fff
def Y2 : ℕ := 0x7ffffc07ffe03f8ffc001fff001fff000fff
def ws2 : List Wr := [⟨0x81020408102040274005bfb000000000000000000000fe03f8ffc001fff000000000000, 0x102040010180060b14000809000000000000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18300101800804e8000000000045000000, 0⟩, ⟨0x40810204081020700000d40500f000005507f01fc000000000e00001fc0001f00000ff0, 0x141050008100040000000540000100000550, 0⟩, ⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x82820008280040000001036000010000005, 0⟩, ⟨0x8102040810204006000429c0000228022a60001fc07f0000000c00007380014cf000dcc, 0x10203000c20008000000020000148a000880, 0⟩, ⟨0xa142850a14285005800523200408e00288afffe000000000000b00004e4000b3c00033f, 0x810500142800a0000000080000a2000022a, 0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub2 : search L2 Y2 7 ws2 0 0 0 0 = false := by decide +kernel
def L3 : ℕ := 0x6a01ab56ad5ab1fc1fe03f0fe0ff03f00f
def Y3 : ℕ := 0xfe03ffffffffb1fc1fe03f0fe0ff03f00f
def ws3 : List Wr := [⟨0x183060c183060c18742af2bb000000000000000000000fe03fb1fc1fe03f000000000000, 0x60018300ac0281140a0009000000000000, 0⟩, ⟨0x2040810204081008a0000000260dd00000000000007f01fffb1fc0000000fe0ff000000, 0x80023108c58b0e80000000b2045000000, 0⟩, ⟨0x10a142850a142858002fa00005900025d000000003f8001fc030001fe0000fe00003f000, 0x4200a2142510800000a00004c000005000, 0⟩, ⟨0x810204081020408005000487007021820500fe00000fe00001001e003f0e00f003000f, 0x6800081680408000140036000010000005, 0⟩, ⟨0x18b162c58b162c50602cc29c048022a562a600000007f0000020c01980380900cf02c00c, 0x620188462c58800000000000008a000000, 0⟩, ⟨0xa142850a14285005800523200408e00288a80fe03f800000000b001e02400803c03f00f, 0x42010942850a000001400000002003a00a, 0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub3 : search L3 Y3 7 ws3 0 0 0 0 = false := by decide +kernel
def L4 : ℕ := 0x7401d3a7401d3a76fce1e7c031e70f1cf1f0
def Y4 : ℕ := 0x7f01fffff01ffff6fce1e7c031e70f1cf1f0
def ws4 : List Wr := [⟨0x3870e1c3870e1c3a757afbfb0000000000000000000000003ff6fce1e7c0000000000000, 0x7001c387001c020214000000000000000000, 0⟩, ⟨0x2040810204081010a00000010638d00000000000007f01ffff6fc00000031e70f000000, 0x4001027001c3874e8000000112005000000, 0⟩, ⟨0x3060c183060c1838017aa0000890000e5000000003f8001fc07000e1e00031e0001cf000, 0x600180a6000530000000a00020c000005000, 0⟩, ⟨0x2040810204081023015009401803000a00507f01fc000000004600e007c03007001c01f0, 0x3400d2040010200000400540000100080150, 0⟩, ⟨0x183060c183060c106028c2980080028460a20001fc07f0000020c0c1870001040f18c1c0, 0x30011184400c18000080020000040a100080, 0⟩, ⟨0xa142850a14285005800523200408e00288aff0003f800000000b021e4c000830c04f130, 0x6000530140050a000021408000020004a020, 0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub4 : search L4 Y4 7 ws4 0 0 0 0 = false := by decide +kernel
def L5 : ℕ := 0x4e9c027009d3a75f3f2678c7f6eb30253233
def Y5 : ℕ := 0x7ffe03f80fffffdf3f2678c7f6eb30253233
def ws5 : List Wr := [⟨0x204081020408102a15523963000000000000000000000fe03fdf3f2678c7000000000000, 0x4080020001d0070b15020801000000000000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc1800600190a15428000000522000000000, 0⟩, ⟨0x2142850a142850a801d320002910005a9000000003f8001fc05003266000f6e000253000, 0x428400600843210000002000a4c000001000, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f0000000000004e032018c0f00b00240230, 0x49402500952a50000000040000100000010, 0⟩, ⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xa8800500882850002041006000010000001, 0⟩, ⟨0x2040810204081001800102200408c000808fffe03f800000000302060c4008b30253233, 0x4a9402500081020000204080000a20252222, 0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub5 : search L5 Y5 7 ws5 0 0 0 0 = false := by decide +kernel
def L6 : ℕ := 0x1ac06bd7af5ff4fde1b1bff74c3d80cc0
def Y6 : ℕ := 0x1fc07ffffffff4fde1b1bff74c3d80cc0
def ws6 : List Wr := [⟨0x3060c183060c183a257aa9c9000000000000000000000fe03fff4fde1b1b000000000000, 0x180060178058b050a0809000000000000, 0⟩, ⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x20063118f1f4480000005b2041000000, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x18c063c62318000000000a44000000000, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05500001fc000000004e03c01b00f01400d80cc0, 0x8404a952a50000400100000000480440, 0⟩, ⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0x2c00bc02c58002141012000000000000, 0⟩, ⟨0x10a142850a142850202c808c048020a542240001fc07f000002040d803180914c3d80cc0, 0x12804a428508000800200001482900880, 0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub6 : search L6 Y6 6 ws6 0 0 0 0 = false := by decide +kernel
def kids : List Kid := [
  ⟨[⟨0x3ffffc000000000000000000, 0x3ffffc000000000000000000, 3⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 126, 64, 0x3ffffc000000000000000000⟩,
  ⟨[⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060fe0307f0180010a0000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 122, 66, 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000⟩,
  ⟨[⟨0xfe00009031e183f000000000000, 0xfe00009031e183f000000000000, 17⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 110, 66, 0xfe00009031e183f000000000000⟩,
  ⟨[⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xbe82c58b162c589010a0809000010000005, 16⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 110, 66, 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f⟩,
  ⟨[⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x103f80fe02040800008000800148a900880, 32⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 94, 66, 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc⟩,
  ⟨[⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x7bf613d84081020010000000000a2027a22a, 64⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩], 127, 126, 2, 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f⟩,
  ⟨[⟨0x1fc07000000000ffe000000000, 0x1fc07000000000ffe000000000, 6⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 123, 64, 0x1fc07000000000ffe000000000⟩,
  ⟨[⟨0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x6fdfbc810de40804e800a000000045005000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 123, 64, 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000⟩,
  ⟨[⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18306731833984e8000000a4c045000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 123, 64, 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000⟩,
  ⟨[⟨0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x810204081020400000000004a0050000000, 18⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 111, 64, 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000⟩,
  ⟨[⟨0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xfe03c7f0e1c3874ea141036112005000005, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 111, 64, 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f⟩,
  ⟨[⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3f80c183f80c180021410364a0040000005, 16⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 111, 64, 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f⟩,
  ⟨[⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc183060c19cf9d42800000052348a000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 95, 64, 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000⟩,
  ⟨[⟨0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x408102040810200a0000000000a24000000, 66⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 127, 0, 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000⟩,
  ⟨[⟨0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0x63c6731e3398f1f4482140805b204127a22a, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 127, 0, 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f⟩,
  ⟨[⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x8102047711dfbf4480000005b2a61000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 127, 0, 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000⟩,
  ⟨[⟨0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x3060c183060c18002140000840000000000, 20⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 107, 66, 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000⟩,
  ⟨[⟨0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x6b29aca6b28535800000b03620c010005005, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 107, 66, 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f⟩,
  ⟨[⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x8ee20408ee2040000001036840010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 107, 66, 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f⟩,
  ⟨[⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x63c78f1e3c67318000214000a4400027a000, 4⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 123, 2, 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000⟩,
  ⟨[⟨0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0xa142850a142850002001000000000400400, 24⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 103, 66, 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00⟩,
  ⟨[⟨0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x3468d25cb692e58000540576000110080155, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 103, 66, 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff⟩,
  ⟨[⟨0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc, 0x4f613d84f7efd800000004000018a000010, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 87, 66, 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc⟩,
  ⟨[⟨0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x10204081020408000100030001080800804, 48⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 79, 66, 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c⟩,
  ⟨[⟨0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x3b8911dc488edd800284120600041a100081, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 79, 66, 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf⟩,
  ⟨[⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xaea2850aea2850002041006001090800801, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 79, 66, 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203⟩,
  ⟨[⟨0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x60c07f01fc07cf800235509200020004a020, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 111, 2, 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f⟩,
  ⟨[⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0xb162c58be82c5800214101200082023020a, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 111, 2, 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootSearch : anyP (tryP LO (rootNext allowed kids) 9 (lenL root) 127 127 66 0) (pairsA [] root) = false := by decide +kernel
def kv0 : List Wr := [⟨0x3ffffc000000000000000000, 0x3ffffc000000000000000000, 3⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid0 : search LO LO 9 kv0 127 126 64 0x3ffffc000000000000000000 = false := by decide +kernel
def kv1 : List Wr := [⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060fe0307f0180010a0000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid1 : search LO LO 9 kv1 127 122 66 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000 = false := by decide +kernel
def kv2 : List Wr := [⟨0xfe00009031e183f000000000000, 0xfe00009031e183f000000000000, 17⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid2 : search LO LO 9 kv2 127 110 66 0xfe00009031e183f000000000000 = false := by decide +kernel
def kv3 : List Wr := [⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xbe82c58b162c589010a0809000010000005, 16⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid3 : search LO LO 9 kv3 127 110 66 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f = false := by decide +kernel
def kv4 : List Wr := [⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x103f80fe02040800008000800148a900880, 32⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid4 : search LO LO 9 kv4 127 94 66 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc = false := by decide +kernel
def kv5 : List Wr := [⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x7bf613d84081020010000000000a2027a22a, 64⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩]
def ck5 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (((pairsA [] kv5).drop (6 * i)).take 6)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_0 : ck5 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_1 : ck5 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_2 : ck5 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_3 : ck5 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_4 : ck5 4 = false := by decide +kernel
theorem kid5 : search LO LO 9 kv5 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f = false := by
  have h1 : isT LO kv5 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (pairsA [] kv5) = false := by
    refine anyP_chunks _ 6 5 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k5_0
    · exact k5_1
    · exact k5_2
    · exact k5_3
    · exact k5_4
  rw [search, h1, h2]; rfl
def kv6 : List Wr := [⟨0x1fc07000000000ffe000000000, 0x1fc07000000000ffe000000000, 6⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid6 : search LO LO 9 kv6 127 123 64 0x1fc07000000000ffe000000000 = false := by decide +kernel
def kv7 : List Wr := [⟨0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x6fdfbc810de40804e800a000000045005000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
def ck7 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_0 : ck7 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_1 : ck7 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_2 : ck7 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_3 : ck7 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_4 : ck7 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_5 : ck7 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_6 : ck7 6 = false := by decide +kernel
theorem kid7 : search LO LO 9 kv7 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000 = false := by
  have h1 : isT LO kv7 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (pairsA [] kv7) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k7_0
    · exact k7_1
    · exact k7_2
    · exact k7_3
    · exact k7_4
    · exact k7_5
    · exact k7_6
  rw [search, h1, h2]; rfl
def kv8 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18306731833984e8000000a4c045000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
def ck8 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (((pairsA [] kv8).drop (5 * i)).take 5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k8_0 : ck8 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k8_1 : ck8 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k8_2 : ck8 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k8_3 : ck8 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k8_4 : ck8 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k8_5 : ck8 5 = false := by decide +kernel
theorem kid8 : search LO LO 9 kv8 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000 = false := by
  have h1 : isT LO kv8 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (pairsA [] kv8) = false := by
    refine anyP_chunks _ 5 6 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k8_0
    · exact k8_1
    · exact k8_2
    · exact k8_3
    · exact k8_4
    · exact k8_5
  rw [search, h1, h2]; rfl
def kv9 : List Wr := [⟨0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x810204081020400000000004a0050000000, 18⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid9 : search LO LO 9 kv9 127 111 64 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000 = false := by decide +kernel
def kv10 : List Wr := [⟨0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xfe03c7f0e1c3874ea141036112005000005, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
def ck10 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k10_0 : ck10 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k10_1 : ck10 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k10_2 : ck10 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k10_3 : ck10 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k10_4 : ck10 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k10_5 : ck10 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k10_6 : ck10 6 = false := by decide +kernel
theorem kid10 : search LO LO 9 kv10 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f = false := by
  have h1 : isT LO kv10 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (pairsA [] kv10) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k10_0
    · exact k10_1
    · exact k10_2
    · exact k10_3
    · exact k10_4
    · exact k10_5
    · exact k10_6
  rw [search, h1, h2]; rfl
def kv11 : List Wr := [⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3f80c183f80c180021410364a0040000005, 16⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid11 : search LO LO 9 kv11 127 111 64 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f = false := by decide +kernel
def kv12 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc183060c19cf9d42800000052348a000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
def ck12 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (((pairsA [] kv12).drop (5 * i)).take 5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k12_0 : ck12 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k12_1 : ck12 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k12_2 : ck12 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k12_3 : ck12 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k12_4 : ck12 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k12_5 : ck12 5 = false := by decide +kernel
theorem kid12 : search LO LO 9 kv12 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000 = false := by
  have h1 : isT LO kv12 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (pairsA [] kv12) = false := by
    refine anyP_chunks _ 5 6 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k12_0
    · exact k12_1
    · exact k12_2
    · exact k12_3
    · exact k12_4
    · exact k12_5
  rw [search, h1, h2]; rfl
def kv13 : List Wr := [⟨0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x408102040810200a0000000000a24000000, 66⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]
def ck13 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k13_0 : ck13 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k13_1 : ck13 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k13_2 : ck13 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k13_3 : ck13 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k13_4 : ck13 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k13_5 : ck13 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k13_6 : ck13 6 = false := by decide +kernel
theorem kid13 : search LO LO 9 kv13 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000 = false := by
  have h1 : isT LO kv13 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (pairsA [] kv13) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k13_0
    · exact k13_1
    · exact k13_2
    · exact k13_3
    · exact k13_4
    · exact k13_5
    · exact k13_6
  rw [search, h1, h2]; rfl
def kv14 : List Wr := [⟨0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0x63c6731e3398f1f4482140805b204127a22a, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]
def ck14 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k14_0 : ck14 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k14_1 : ck14 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k14_2 : ck14 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k14_3 : ck14 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k14_4 : ck14 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k14_5 : ck14 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k14_6 : ck14 6 = false := by decide +kernel
theorem kid14 : search LO LO 9 kv14 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f = false := by
  have h1 : isT LO kv14 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (pairsA [] kv14) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k14_0
    · exact k14_1
    · exact k14_2
    · exact k14_3
    · exact k14_4
    · exact k14_5
    · exact k14_6
  rw [search, h1, h2]; rfl
def kv15 : List Wr := [⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x8102047711dfbf4480000005b2a61000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]
def ck15 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15_0 : ck15 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15_1 : ck15 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15_2 : ck15 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15_3 : ck15 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15_4 : ck15 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15_5 : ck15 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15_6 : ck15 6 = false := by decide +kernel
theorem kid15 : search LO LO 9 kv15 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000 = false := by
  have h1 : isT LO kv15 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (pairsA [] kv15) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k15_0
    · exact k15_1
    · exact k15_2
    · exact k15_3
    · exact k15_4
    · exact k15_5
    · exact k15_6
  rw [search, h1, h2]; rfl
def kv16 : List Wr := [⟨0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x3060c183060c18002140000840000000000, 20⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid16 : search LO LO 9 kv16 127 107 66 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000 = false := by decide +kernel
def kv17 : List Wr := [⟨0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x6b29aca6b28535800000b03620c010005005, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
def ck17 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k17_0 : ck17 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k17_1 : ck17 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k17_2 : ck17 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k17_3 : ck17 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k17_4 : ck17 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k17_5 : ck17 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k17_6 : ck17 6 = false := by decide +kernel
theorem kid17 : search LO LO 9 kv17 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f = false := by
  have h1 : isT LO kv17 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (pairsA [] kv17) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k17_0
    · exact k17_1
    · exact k17_2
    · exact k17_3
    · exact k17_4
    · exact k17_5
    · exact k17_6
  rw [search, h1, h2]; rfl
def kv18 : List Wr := [⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x8ee20408ee2040000001036840010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid18 : search LO LO 9 kv18 127 107 66 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f = false := by decide +kernel
def kv19 : List Wr := [⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x63c78f1e3c67318000214000a4400027a000, 4⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid19 : search LO LO 9 kv19 127 123 2 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000 = false := by decide +kernel
def kv20 : List Wr := [⟨0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0xa142850a142850002001000000000400400, 24⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid20 : search LO LO 9 kv20 127 103 66 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00 = false := by decide +kernel
def kv21 : List Wr := [⟨0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x3468d25cb692e58000540576000110080155, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
def ck21 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k21_0 : ck21 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k21_1 : ck21 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k21_2 : ck21 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k21_3 : ck21 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k21_4 : ck21 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k21_5 : ck21 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k21_6 : ck21 6 = false := by decide +kernel
theorem kid21 : search LO LO 9 kv21 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff = false := by
  have h1 : isT LO kv21 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (pairsA [] kv21) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k21_0
    · exact k21_1
    · exact k21_2
    · exact k21_3
    · exact k21_4
    · exact k21_5
    · exact k21_6
  rw [search, h1, h2]; rfl
def kv22 : List Wr := [⟨0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc, 0x4f613d84f7efd800000004000018a000010, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
def ck22 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k22_0 : ck22 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k22_1 : ck22 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k22_2 : ck22 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k22_3 : ck22 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k22_4 : ck22 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k22_5 : ck22 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k22_6 : ck22 6 = false := by decide +kernel
theorem kid22 : search LO LO 9 kv22 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc = false := by
  have h1 : isT LO kv22 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (pairsA [] kv22) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k22_0
    · exact k22_1
    · exact k22_2
    · exact k22_3
    · exact k22_4
    · exact k22_5
    · exact k22_6
  rw [search, h1, h2]; rfl
def kv23 : List Wr := [⟨0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x10204081020408000100030001080800804, 48⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid23 : search LO LO 9 kv23 127 79 66 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c = false := by decide +kernel
def kv24 : List Wr := [⟨0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x3b8911dc488edd800284120600041a100081, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
def ck24 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k24_0 : ck24 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k24_1 : ck24 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k24_2 : ck24 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k24_3 : ck24 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k24_4 : ck24 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k24_5 : ck24 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k24_6 : ck24 6 = false := by decide +kernel
theorem kid24 : search LO LO 9 kv24 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf = false := by
  have h1 : isT LO kv24 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (pairsA [] kv24) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k24_0
    · exact k24_1
    · exact k24_2
    · exact k24_3
    · exact k24_4
    · exact k24_5
    · exact k24_6
  rw [search, h1, h2]; rfl
def kv25 : List Wr := [⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xaea2850aea2850002041006001090800801, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid25 : search LO LO 9 kv25 127 79 66 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203 = false := by decide +kernel
def kv26 : List Wr := [⟨0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x60c07f01fc07cf800235509200020004a020, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]
def ck26 (i : ℕ) : Bool := anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (4 * i)).take 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k26_0 : ck26 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k26_1 : ck26 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k26_2 : ck26 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k26_3 : ck26 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k26_4 : ck26 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k26_5 : ck26 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k26_6 : ck26 6 = false := by decide +kernel
theorem kid26 : search LO LO 9 kv26 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f = false := by
  have h1 : isT LO kv26 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (pairsA [] kv26) = false := by
    refine anyP_chunks _ 4 7 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact k26_0
    · exact k26_1
    · exact k26_2
    · exact k26_3
    · exact k26_4
    · exact k26_5
    · exact k26_6
  rw [search, h1, h2]; rfl
def kv27 : List Wr := [⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0xb162c58be82c5800214101200082023020a, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid27 : search LO LO 9 kv27 127 111 2 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00 = false := by decide +kernel
theorem kids_false : ∀ q ∈ kids, search LO LO 9 q.v q.c1 q.c2 q.c3 q.g = false := by
  intro q hq
  simp only [kids, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kid0
  · exact kid1
  · exact kid2
  · exact kid3
  · exact kid4
  · exact kid5
  · exact kid6
  · exact kid7
  · exact kid8
  · exact kid9
  · exact kid10
  · exact kid11
  · exact kid12
  · exact kid13
  · exact kid14
  · exact kid15
  · exact kid16
  · exact kid17
  · exact kid18
  · exact kid19
  · exact kid20
  · exact kid21
  · exact kid22
  · exact kid23
  · exact kid24
  · exact kid25
  · exact kid26
  · exact kid27
def okL (L y : ℕ) : Bool :=
  Nat.blt L (2 ^ 143) && (List.range 143).all fun i => !(L.testBit i) || (y.testBit i != y.testBit (143 + i))
lemma okL_spec {L y : ℕ} (h : okL L y = true) (i : ℕ) (hi : L.testBit i = true) :
    y.testBit i ≠ y.testBit (143 + i) := by
  rw [okL, Bool.and_eq_true] at h
  have hlt : i < 143 := by
    by_contra hc
    have h1 : L < 2 ^ 143 := by simpa [Nat.blt_eq] using h.1
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (not_lt.mp hc)))
    rw [this] at hi
    exact Bool.false_ne_true hi
  have h2 := List.all_eq_true.mp h.2 i (List.mem_range.mpr hlt)
  rw [hi] at h2
  simpa using h2
def W0 : Set ℕ := {x | x = 0 ∨ ∃ i : Fin 7, x = ip i}
def LB (h : ℕ) : ℕ := [8, 7, 8, 8, 8, 8, 7].getD h 0
lemma subW (h : ℕ) (ws : List Wr)
    (hc : ∀ i : Fin 7, Nat.land (ip i) (mask h) = 0 ∨ ∃ u ∈ ws, u.w = Nat.land (ip i) (mask h))
    {W : Set ℕ} (hW : ∀ x ∈ W, x = 0 ∨ ∃ i : Fin 7, x = Nat.land (ip i) (mask h)) :
    ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x := by
  intro x hx
  rcases hW x hx with e | ⟨i, e⟩
  · exact Or.inl e
  · rw [e]; exact hc i
theorem subBound (h : ℕ) (hh : h < 7) {W : Set ℕ} (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ i : Fin 7, x = Nat.land (ip i) (mask h)) :
    ¬ Der opN (LB h - 1) W (Nat.land LO (mask h)) := by
  interval_cases h
  · exact refute (L := L0) (y := Y0) (ws := ws0) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub0 h0
      (subW 0 ws0 (by decide +kernel) hW)
  · exact refute (L := L1) (y := Y1) (ws := ws1) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub1 h0
      (subW 1 ws1 (by decide +kernel) hW)
  · exact refute (L := L2) (y := Y2) (ws := ws2) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub2 h0
      (subW 2 ws2 (by decide +kernel) hW)
  · exact refute (L := L3) (y := Y3) (ws := ws3) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub3 h0
      (subW 3 ws3 (by decide +kernel) hW)
  · exact refute (L := L4) (y := Y4) (ws := ws4) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub4 h0
      (subW 4 ws4 (by decide +kernel) hW)
  · exact refute (L := L5) (y := Y5) (ws := ws5) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub5 h0
      (subW 5 ws5 (by decide +kernel) hW)
  · exact refute (L := L6) (y := Y6) (ws := ws6) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub6 h0
      (subW 6 ws6 (by decide +kernel) hW)
lemma root_ip : ∀ i : Fin 7, ∃ u ∈ root, u.w = ip i := by decide +kernel
lemma ip_root : ∀ u ∈ root, ∃ i : Fin 7, u.w = ip i := by decide +kernel
lemma ip_lt : ∀ i : Fin 7, ip i < 2 ^ 286 := by decide +kernel
lemma LO_lt : LO < 2 ^ 286 := by decide +kernel
lemma Tn_inv : ∀ p : Fin 3, ∀ i : Fin 286,
    sIdx (Tn p) i.val < 286 ∧ sIdx (Tn p) (sIdx (Tn p) i.val) = i.val := by decide +kernel
lemma Tn_ip : ∀ p : Fin 3, ∀ i : Fin 7, ∀ r : Fin 286,
    (ip (pm p i)).testBit r.val = (ip i).testBit (sIdx (Tn p) r.val) := by decide +kernel
lemma Tn_LO : ∀ p : Fin 3, ∀ r : Fin 286,
    LO.testBit r.val = LO.testBit (sIdx (Tn p) r.val) := by decide +kernel
lemma pm_inv : ∀ p : Fin 3, ∀ i : Fin 7, pm p (pm p i) = i := by decide
lemma allowed_spec : ∀ t : Fin 4, ∀ i j : Fin 7, i ≠ j →
    (∀ p : Fin 3, opN t (ip i) (ip j) ≤ opN t (ip (pm p i)) (ip (pm p j))) →
    memN (opN t (ip i) (ip j)) allowed = true := by decide +kernel
lemma sg_ip (p : Fin 3) (i : Fin 7) : sg 286 (Tn p) (ip i) = ip (pm p i) :=
  sg_eq (bdd_of_lt (ip_lt _)) fun r hr => Tn_ip p i ⟨r, hr⟩
lemma sg_LO (p : Fin 3) : sg 286 (Tn p) LO = LO :=
  sg_eq (bdd_of_lt LO_lt) fun r hr => Tn_LO p ⟨r, hr⟩
lemma sg_zero (N T : ℕ) : sg N T 0 = 0 :=
  sg_eq (fun i _ => Nat.zero_testBit i) fun r _ => by rw [Nat.zero_testBit, Nat.zero_testBit]
lemma sg_W0 (p : Fin 3) : sg 286 (Tn p) '' W0 = W0 := by
  ext x
  constructor
  · rintro ⟨w, rfl | ⟨i, rfl⟩, rfl⟩
    · exact Or.inl (sg_zero _ _)
    · exact Or.inr ⟨pm p i, sg_ip p i⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, Or.inl rfl, sg_zero _ _⟩
    · exact ⟨ip (pm p i), Or.inr ⟨pm p i, rfl⟩, by rw [sg_ip, pm_inv]⟩
lemma bdd_W0 : ∀ x ∈ W0, Bdd 286 x := by
  rintro x (rfl | ⟨i, rfl⟩)
  · exact fun i _ => Nat.zero_testBit i
  · exact bdd_of_lt (ip_lt i)
theorem theta : ¬ Der opN 10 W0 LO := by
  intro h
  obtain ⟨l, hk, hV, hU, hC, hmin⟩ := exists_sorted h
  have h0 : (0 : ℕ) ∈ W0 := Or.inl rfl
  have hLO : LO ≠ 0 := by decide +kernel
  have hL : ∀ i, LO.testBit i = true → LO.testBit i ≠ LO.testBit (143 + i) :=
    fun i hi => okL_spec (L := LO) (y := LO) (by decide +kernel) i hi
  have caps : ∀ h < 7, kills (mask h) l + LB h ≤ 10 := by
    intro h hh
    obtain ⟨n, hn, hd⟩ := der_masked (m := mask h) l hV h0
    by_contra hc
    have hLB : 1 ≤ LB h := by interval_cases h <;> decide
    refine subBound h hh (W := (fun w => Nat.land w (mask h)) '' W0) ⟨0, h0, by simp [Nat.land]⟩ ?_
      (hd.le (by omega))
    rintro _ ⟨w, rfl | ⟨i, rfl⟩, rfl⟩
    · left; show Nat.land 0 (mask h) = 0; simp [Nat.land]
    · exact Or.inr ⟨i, rfl⟩
  have hy : ∀ h < 7, Nat.land LO (mask h) ≠ 0 := by
    intro h hh
    have key : ∀ h : Fin 7, Nat.land LO (mask h.val) ≠ 0 := by decide +kernel
    exact key ⟨h, hh⟩
  have hfl : ∀ u ∈ root, ∀ h, u.f.testBit h = true → h < 7 ∧ Nat.land u.w (mask h) = 0 := by
    have k1 : ∀ u ∈ root, u.f < 2 ^ 7 := by decide +kernel
    have k2 : ∀ u ∈ root, ∀ h : Fin 7, u.f.testBit h.val = true → Nat.land u.w (mask h.val) = 0 := by
      decide +kernel
    intro u hu h hb
    have hlt : h < 7 := by
      by_contra hc
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (k1 u hu)
        (Nat.pow_le_pow_right (by omega) (not_lt.mp hc)))
      rw [this] at hb
      exact Bool.false_ne_true hb
    exact ⟨hlt, k2 u hu ⟨h, hlt⟩ hb⟩
  have hrep : Rep LO 7 mask root (need LO l) := by
    refine root_rep hL hLO (by decide +kernel) (by decide +kernel) hfl (by decide +kernel) hV h0 ?_
    rintro x (rfl | ⟨i, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (root_ip i)
  have hbud : Bud 7 mask 127 127 66 l := by
    intro h hh
    have c := caps h hh
    interval_cases h <;> simp only [LB, List.getD_cons_zero, List.getD_cons_succ] at c <;>
      refine ⟨by omega, fun _ => by decide, fun _ => by decide, fun h3 => ?_⟩ <;>
      first | (exfalso; omega) | decide
  cases l with
  | nil =>
    have e : ∀ i : Fin 7, LO ≠ ip i := by decide +kernel
    rcases hV with h | ⟨i, h⟩
    · exact hLO h
    · exact e i h
  | cons s l =>
    have al : memN s.val allowed = true := by
      obtain ⟨fa, fb, fab, _⟩ := step_facts hV h0
      rcases hV.1 with e | ⟨i, ei⟩
      · exact absurd e fa
      rcases hV.2.1 with e | ⟨j, ej⟩
      · exact absurd e fb
      have hs : s.val = opN s.t (ip i) (ip j) := by rw [St.val, ei, ej]
      rw [hs]
      refine allowed_spec s.t i j (fun e => fab (by rw [ei, ej, e])) fun p => ?_
      have vm := valid_map (Tn p) (fun i hi => Tn_inv p ⟨i, hi⟩) (s :: l) bdd_W0 hV
      rw [sg_LO, sg_W0] at vm
      have := hmin _ vm (by simp)
      change s.val ≤ (mapSt 286 (Tn p) s).val at this
      rw [mapSt_val, hs, sg_op, sg_ip, sg_ip] at this
      exact this
    have := level (k := 9) (r := rootNext allowed kids) hy hL hV h0 hU (by simpa using hk) hC hrep hbud ?_
    · rw [rootSearch] at this
      exact Bool.false_ne_true this
    · intro v' d1 d2 d3 hv' hb'
      show cond (memN s.val allowed) (!(isKid v' d1 d2 d3 s.val kids)) false = true
      rw [al, cond_true]
      cases hkid : isKid v' d1 d2 d3 s.val kids
      · rfl
      · have hm := kids_false _ (isKid_mem kids hkid)
        have hs := search_complete hy hL 9 l _ v' s.val d1 d2 d3 hV.2.2.2 (Or.inr h0) hU.2
          (by simp only [List.length_cons] at hk; omega) hC.2 hv' hb'
        simp only at hm
        rw [hm] at hs
        exact absurd hs Bool.false_ne_true
abbrev Om := Fin 9 → Bool
def zr : Om := fun _ => false
def nrm (F : Om → Bool) : Om → Bool := fun x => F x != F zr
def bc (gs : List Gate) : ℕ := gs.countP fun g => !(g.op.eval [false])
def nc (gs : List Gate) : ℕ := gs.countP fun g => g.op.eval [false]
def runG (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
def OkG (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i = w.length
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right h]
    by_cases h1 : i < w.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    · have h2 : (w ++ [b]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h2,
        List.getElem?_eq_none (by omega : w.length ≤ i)]
lemma nrm_const (c : Bool) : nrm (fun _ => c) = fun _ => false := by
  funext x; simp [nrm]
lemma nrm_not (F : Om → Bool) : nrm (fun x => !(F x)) = nrm F := by
  funext x; simp only [nrm]; cases F x <;> cases F zr <;> rfl
lemma nrm_bin (c : Bool) (F G : Om → Bool) : ∃ t : Fin 4,
    nrm (fun x => if c then (F x || G x) else (F x && G x)) = opF t (nrm F) (nrm G) := by
  cases hc : c <;> cases hF : F zr <;> cases hG : G zr
  · exact ⟨0, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨2, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨3, by funext x; simp [nrm, opF, opB, hF, hG]; cases F x <;> cases G x <;> rfl⟩
  · exact ⟨1, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨1, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨3, by funext x; simp [nrm, opF, opB, hF, hG]; cases F x <;> cases G x <;> rfl⟩
  · exact ⟨2, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨0, by funext x; simp [nrm, opF, opB, hF, hG]⟩
lemma circ (gs : List Gate) : ∀ (w : Om → List Bool) (m : ℕ) (U : Set (Om → Bool)),
    (∀ x, (w x).length = m) → (fun _ => false) ∈ U →
    (∀ i, nrm (fun x => (w x).getD i false) ∈ U) → (∀ g ∈ gs, OkG g) →
    ∀ o, Der opF (bc gs) U (nrm fun x => (runG gs (w x)).getD o false) := by
  induction gs with
  | nil => intro w m U _ _ hU _ o; exact Der.here (hU o)
  | cons g gs ih =>
    intro w m U hl h0 hU hg o
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    have hgs : ∀ g' ∈ gs, OkG g' := fun g' h => hg g' (by simp [h])
    let v : Om → Bool := fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
    let w' : Om → List Bool := fun x => w x ++ [v x]
    have hl' : ∀ x, (w' x).length = m + 1 := fun x => by simp [w', hl]
    have hw' (U' : Set (Om → Bool)) (hs : U ⊆ U') (hv : nrm v ∈ U') :
        ∀ i, nrm (fun x => (w' x).getD i false) ∈ U' := by
      intro i
      by_cases hi : i = m
      · have e : (fun x => (w' x).getD i false) = v := by
          funext x; simp only [w']; rw [getD_snoc, ite_eq_left (by rw [hl, hi])]
        rw [e]; exact hv
      · have e : (fun x => (w' x).getD i false) = fun x => (w x).getD i false := by
          funext x; simp only [w']; rw [getD_snoc, ite_eq_right (by rw [hl]; exact hi)]
        rw [e]; exact hs (hU i)
    have fin0 (hv : nrm v ∈ U) : Der opF (bc gs) U (nrm fun x => (runG (g :: gs) (w x)).getD o false) :=
      ih w' (m + 1) U hl' h0 (hw' U (fun _ h => h) hv) hgs o
    have bcle : bc gs ≤ bc (g :: gs) := by
      rw [bc, bc, List.countP_cons]; omega
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have bin (c : Bool) (hb : bc (g :: gs) = bc gs + 1)
        (hev : ∀ l : List Bool, g.op.eval l = if c then l.any id else l.all id) :
        Der opF (bc (g :: gs)) U (nrm fun x => (runG (g :: gs) (w x)).getD o false) := by
      rcases hi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨q, r⟩⟩⟩
      · refine (fin0 ?_).le bcle
        have e : v = fun _ => !c := by
          funext x; simp only [v, hi, hev]; cases c <;> rfl
        rw [e, nrm_const]; exact h0
      · refine (fin0 ?_).le bcle
        have e : v = fun x => (w x).getD i false := by
          funext x; simp only [v, hi, hev]; cases c <;> simp
        rw [e]; exact hU i
      · obtain ⟨t, ht⟩ := nrm_bin c (fun x => (w x).getD i false) (fun x => (w x).getD j false)
        have e : v = fun x => if c then ((w x).getD i false || (w x).getD j false)
            else ((w x).getD i false && (w x).getD j false) := by
          funext x; simp only [v, hi, hev]; cases c <;> simp
        have ev : nrm v = opF t (nrm fun x => (w x).getD i false) (nrm fun x => (w x).getD j false) := by
          rw [e]; exact ht
        rw [hb]
        refine Der.step t _ _ (hU i) (hU j) ?_
        refine ih w' (m + 1) _ hl' (Or.inr h0) (hw' _ (Set.subset_insert _ _) ?_) hgs o
        rw [ev]; exact Or.inl rfl
      · rw [hi] at hlen; simp at hlen
    rcases hop with h | h | h
    · refine bin false ?_ (fun l => by rw [h]; rfl)
      rw [bc, bc, List.countP_cons, h]; rfl
    · refine bin true ?_ (fun l => by rw [h]; rfl)
      rw [bc, bc, List.countP_cons, h]; rfl
    · refine (fin0 ?_).le bcle
      rcases hi : g.inputs with _ | ⟨i, r⟩
      · have e : v = fun _ => true := by funext x; simp only [v, hi, h]; rfl
        rw [e, nrm_const]; exact h0
      · have e : v = fun x => !((w x).getD i false) := by funext x; simp only [v, hi, h]; rfl
        rw [e, nrm_not]; exact hU i
def fG : Om → Bool := fun x =>
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def pin (j : Fin 9) (F : Om → Bool) : Om → Bool := fun x => F (Function.update x j false)
def rowTab (j : Fin 9) : ℕ := [0, ip 0, ip 1, ip 2, 0, ip 3, ip 4, ip 5, ip 6].getD j.val 0
def row (r : Fin 286) : Om := fun j => (rowTab j).testBit r.val
def encF (F : Om → Bool) : ℕ := Nat.ofBits fun r : Fin 286 => F (row r)
lemma encF_bit (F : Om → Bool) (i : ℕ) (hi : i < 286) : (encF F).testBit i = F (row ⟨i, hi⟩) := by
  rw [encF, Nat.testBit_ofBits_lt _ _ hi]
lemma encF_bdd (F : Om → Bool) : Bdd 286 (encF F) := fun i hi => by
  rw [encF, Nat.testBit_ofBits_ge _ _ hi]
lemma encF_op (t : Fin 4) (F G : Om → Bool) : encF (opF t F G) = opN t (encF F) (encF G) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 286
  · rw [opN_bit, encF_bit _ _ hi, encF_bit _ _ hi, encF_bit _ _ hi]; rfl
  · rw [encF_bdd _ i (by omega), bdd_op t (encF_bdd F) (encF_bdd G) i (by omega)]
lemma encF_eq {F : Om → Bool} {x : ℕ} (hx : Bdd 286 x) (h : ∀ r : Fin 286, F (row r) = x.testBit r.val) :
    encF F = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 286
  · rw [encF_bit _ _ hi]; exact h ⟨i, hi⟩
  · rw [encF_bdd _ i (by omega), hx i (by omega)]
lemma fG_rows : ∀ r : Fin 286, pin 4 (pin 0 fG) (row r) = LO.testBit r.val := by decide +kernel
lemma opF_false_left (t : Fin 4) (F : Om → Bool) :
    opF t (fun _ => false) F = (fun _ => false) ∨ opF t (fun _ => false) F = F := by
  fin_cases t
  · left; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
  · left; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
lemma opF_false_right (t : Fin 4) (F : Om → Bool) :
    opF t F (fun _ => false) = (fun _ => false) ∨ opF t F (fun _ => false) = F := by
  fin_cases t
  · left; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
  · left; funext x; simp [opF, opB]
def pt (l : List (Fin 9)) : Om := fun j => l.contains j
theorem noDer (b : Fin 9) (hb : b = 1) :
    ¬ Der opF 12 {F : Om → Bool | F = (fun _ => false) ∨ (∃ i : Fin 9, F = fun x => x i) ∨
      F = fun x => x 0 || x b} fG := by
  intro h
  have hb0 : b ≠ 0 := by subst hb; decide
  have e0 : pin 0 (fun x : Om => x 0) = fun _ => false := by funext x; simp [pin]
  have e0z : pin 0 (fun _ : Om => false) = fun _ => false := rfl
  have e0i (i : Fin 9) (hi : i ≠ 0) : pin 0 (fun x : Om => x i) = fun x => x i := by
    funext x; simp [pin, Function.update_of_ne hi]
  have e0g : pin 0 (fun x : Om => x 0 || x b) = fun x => x b := by
    funext x; simp [pin, Function.update_of_ne hb0]
  have hE := h.elim (op' := opF) (pin 0) (fun _ _ _ => rfl) (fun x => x 0)
    (fun t F => by rw [e0]; exact opF_false_left t F) (fun t F => by rw [e0]; exact opF_false_right t F)
    {F : Om → Bool | F = (fun _ => false) ∨ (∃ i : Fin 9, i ≠ 0 ∧ F = fun x => x i) ∨
      F = fun x => x 0 || x b}
    (by
      rintro F (rfl | ⟨i, rfl⟩ | rfl)
      · exact Or.inr (Or.inl rfl)
      · by_cases hi : i = 0
        · subst hi; exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr rfl)))
    (by
      intro e
      have := congrFun e (pt [0])
      revert this; decide)
    ⟨fun _ => false, Or.inl rfl, by rw [e0]; rfl⟩
  rcases hE with h | ⟨k', hk', h⟩
  · have := h.agree (pt [0, b, 5]) (pt [b, 5]) (by
      rintro F (rfl | ⟨i, hi, rfl⟩ | rfl)
      · rfl
      · subst hb; revert hi; revert i; decide
      · subst hb; decide)
    revert this; subst hb; decide
  · have hk : k' = 11 := by omega
    subst hk
    have e4 : pin 4 (fun x : Om => x 4) = fun _ => false := by funext x; simp [pin]
    have e4i (i : Fin 9) (hi : i ≠ 4) : pin 4 (fun x : Om => x i) = fun x => x i := by
      funext x; simp [pin, Function.update_of_ne hi]
    have hE := h.elim (op' := opF) (pin 4) (fun _ _ _ => rfl) (fun x => x 4)
      (fun t F => by rw [e4]; exact opF_false_left t F)
      (fun t F => by rw [e4]; exact opF_false_right t F)
      {F : Om → Bool | F = (fun _ => false) ∨ ∃ i : Fin 9, i ≠ 0 ∧ i ≠ 4 ∧ F = fun x => x i}
      (by
        rintro _ ⟨F, hF, rfl⟩
        rcases hF with rfl | ⟨i, hi, rfl⟩ | rfl
        · exact Or.inr (Or.inl rfl)
        · rw [e0i i hi]
          by_cases h4 : i = 4
          · subst h4; exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨i, hi, h4, rfl⟩)
        · rw [e0g]
          exact Or.inr (Or.inr ⟨b, hb0, by subst hb; decide, rfl⟩))
      (by
        intro e
        have := congrFun e (pt [4])
        revert this; decide)
      ⟨fun _ => false, Or.inl rfl, by rw [e4]; rfl⟩
    rcases hE with h | ⟨k', hk', h⟩
    · have := h.agree (pt [3, 4]) (pt [3]) (by
        rintro F (rfl | ⟨i, h1, h2, rfl⟩)
        · rfl
        · revert h1 h2; revert i; decide)
      revert this; decide
    · have hk : k' = 10 := by omega
      subst hk
      have hN := h.map (op' := opN) encF encF_op
      rw [encF_eq (bdd_of_lt LO_lt) fG_rows] at hN
      refine theta (hN.mono ?_)
      rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
      rcases hF with rfl | ⟨i, h1, h2, rfl⟩
      · left
        exact encF_eq (fun i _ => Nat.zero_testBit i) fun r => by rw [Nat.zero_testBit]; rfl
      · right
        rw [e4i i h2]
        have hr : ∀ i : Fin 9, i ≠ 0 → i ≠ 4 → ∃ j : Fin 7, rowTab i = ip j := by decide +kernel
        obtain ⟨j, hj⟩ := hr i h1 h2
        exact ⟨j, encF_eq (bdd_of_lt (ip_lt j)) fun r => by show (rowTab i).testBit _ = _; rw [hj]⟩
lemma ofFn_getD (n : ℕ) (y : Fin n → Bool) (i : ℕ) :
    (List.ofFn y).getD i false = if h : i < n then y ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dif_pos h]; simp [List.getD_eq_getElem?_getD, h]
  · rw [dif_neg h]; simp [List.getD_eq_getElem?_getD, h]
lemma two_count {α : Type} (p : α → Bool) (l : List α) (i j : ℕ) (hij : i < j) (hj : j < l.length)
    (h1 : p (l[i]'(by omega)) = true) (h2 : p l[j] = true) : 2 ≤ l.countP p := by
  rw [← List.take_append_drop j l, List.countP_append]
  have a1 : 1 ≤ (l.take j).countP p := by
    rw [Nat.succ_le_iff, List.countP_pos_iff]
    refine ⟨l[i]'(by omega), ?_, h1⟩
    rw [List.mem_take_iff_getElem]
    exact ⟨i, by omega, rfl⟩
  have a2 : 1 ≤ (l.drop j).countP p := by
    rw [Nat.succ_le_iff, List.countP_pos_iff]
    refine ⟨l[j], ?_, h2⟩
    rw [List.mem_drop_iff_getElem]
    exact ⟨0, by omega, by simp⟩
  omega
theorem no15 (b : Fin 9) (hb : b = 1) (C : Circuit) (hC : FanInTwo C) (hsize : C.size ≤ 15)
    (hw : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y b))
    (hn : 2 ≤ nc C.gates) (hf : circuitFun 9 C = fG) : False := by
  obtain ⟨gates, out⟩ := C
  cases gates with
  | nil => simp [nc] at hn
  | cons g gs =>
    have hlen : gs.length ≤ 14 := by
      have : (Circuit.mk (g :: gs) out).size = gs.length + 1 := rfl
      omega
    have hg0 := hC g (by simp)
    have hfirst (x : Om) : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x b) := by
      have h := hw x
      change (runG gs (List.ofFn x ++ [_])).getD 9 false = _ at h
      have keep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
          (runG gs w).getD i false = w.getD i false := by
        intro gs
        induction gs with
        | nil => intro w i _; rfl
        | cons q gs ih =>
          intro w i hi
          change (runG gs (w ++ [_])).getD i false = _
          rw [ih _ i (by simp; omega), getD_snoc, ite_eq_right (by omega)]
      rw [keep _ _ _ (by simp), getD_snoc, ite_eq_left (by simp)] at h
      exact h
    have hnot : g.op.eval [false] = false := by
      rcases hg0.1 with h | h | h
      · rw [h]; rfl
      · rw [h]; rfl
      · exfalso
        have := hfirst zr
        rw [h] at this
        have hz : ∀ i, (List.ofFn zr).getD i false = false := by
          intro i
          rw [ofFn_getD]
          split_ifs <;> rfl
        rcases hi : g.inputs with _ | ⟨i, r⟩
        · rw [hi] at this; revert this; simp [GateOp.eval, zr]
        · rw [hi] at this
          simp only [List.map_cons, hz] at this
          revert this; simp [GateOp.eval, zr]
    have hnc : nc (g :: gs) = nc gs := by
      rw [nc, nc, List.countP_cons, hnot]; rfl
    have hn' : 2 ≤ nc gs := by rw [← hnc]; exact hn
    have hsum : gs.length = nc gs + bc gs := by
      have := List.length_eq_countP_add_countP (fun g : Gate => g.op.eval [false]) (l := gs)
      rw [this, nc, bc]
      congr 1
    let U : Set (Om → Bool) := {F | F = (fun _ => false) ∨ (∃ i : Fin 9, F = fun x => x i) ∨
      F = fun x => x 0 || x b}
    have hD : Der opF (bc gs) U (nrm fun x => (runG gs (List.ofFn x ++ [x 0 || x b])).getD out false) := by
      refine circ gs (fun x => List.ofFn x ++ [x 0 || x b]) 10 U (fun x => by simp) (Or.inl rfl) ?_
        (fun q hq => hC q (by simp [hq])) out
      intro i
      by_cases h9 : i = 9
      · right; right
        funext x
        simp only [nrm, getD_snoc, List.length_ofFn, ite_eq_left h9]
        simp [zr]
      · by_cases hi : i < 9
        · right; left
          refine ⟨⟨i, hi⟩, ?_⟩
          funext x
          simp only [nrm, getD_snoc, List.length_ofFn, ite_eq_right h9, ofFn_getD, dif_pos hi]
          simp [zr]
        · left
          funext x
          simp only [nrm, getD_snoc, List.length_ofFn, ite_eq_right h9, ofFn_getD, dif_neg hi]
          rfl
    have he : (nrm fun x => (runG gs (List.ofFn x ++ [x 0 || x b])).getD out false) = fG := by
      have e : (fun x : Om => (runG gs (List.ofFn x ++ [x 0 || x b])).getD out false) = fG := by
        rw [← hf]
        funext x
        rw [← hfirst x]
        rfl
      rw [e]
      funext x
      have : fG zr = false := by decide
      simp [nrm, this]
    rw [he] at hD
    exact noDer b hb (hD.le (by omega))
lemma nc_two {gates : List Gate} (i j : Fin gates.length) (hij : i ≠ j)
    (hi : (gates.get i).op = GateOp.not) (hj : (gates.get j).op = GateOp.not) : 2 ≤ nc gates := by
  have pi : (gates[i.val]'i.isLt).op.eval [false] = true := by
    have : (gates[i.val]'i.isLt).op = GateOp.not := hi
    rw [this]; rfl
  have pj : (gates[j.val]'j.isLt).op.eval [false] = true := by
    have : (gates[j.val]'j.isLt).op = GateOp.not := hj
    rw [this]; rfl
  rcases lt_or_gt_of_ne (fun e => hij (Fin.ext e) : i.val ≠ j.val) with h | h
  · exact two_count _ gates i.val j.val h j.isLt pi pj
  · exact two_count _ gates j.val i.val h i.isLt pj pi
end P1
namespace P2
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))
private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]
private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _
private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v
def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a
inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩
theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]
theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]
theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih
theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega
abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩
theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r
theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _
theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)
theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]
theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]
theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm
theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs
theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 3) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl
theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv
theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega
def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega
def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p
def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)
theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h
theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))
theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv
abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)
theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)
def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none
theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)
theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega
abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]
theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp
theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _
theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm
def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))
theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩
theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL
def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)
theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)
theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩
def apart (m j : Nat) : Bool := m.testBit 9 && (j==0 || j==3)
def word (m j : Nat) : Sig := if apart m j then inputs.getD j zero &&& ~~~seed else inputs.getD j zero
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,word m i) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then word m j else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) :=
  let f := m ^^^ (m &&& (z ||| o))
  if f.testBit 9 && ((z ||| o) &&& 9) != 0 then f ^^^ 512 else f
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)
def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig
def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True
theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩
theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)
theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he
abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]
def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)
def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def wordCol (m : Nat) (v : Nat → Bits) (j : Nat) : Bits :=
  if apart m j then v j &&& ~~~(v 0 &&& v 3) else v j
theorem seed_word : seed = inputs.getD 0 zero &&& inputs.getD 3 zero := by decide +kernel
theorem word_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (word m j.val) = (wordCol m v j.val).getLsbD i.val := by
  by_cases h : apart m j.val = true
  · have e := asRow_bit v i j
    have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (3 : Fin 9)
    change (inputs.getD j.val zero).getLsbD (asRow v i).val = _ at e
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 3 zero).getLsbD (asRow v i).val = (v 3).getLsbD i.val at w
    rw [word,wordCol,if_pos h,if_pos h,seed_word]
    simp only [bit,BitVec.getLsbD_and,BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,e,u,w]
  · rw [word,wordCol,if_neg h,if_neg h]
    exact asRow_bit v i j
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,wordCol m p j,wordCol m q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=word m j := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (word_bit m p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (word_bit m q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then wordCol m v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then wordCol m v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using word_bit m v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then wordCol m v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb
theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha
theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl
def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0
def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)
theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb
theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka
theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]
def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb
abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h
def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs
theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm
theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail
theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all
theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto
theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh
theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)
structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)
def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask _ _
def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)
def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]
def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega
abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)
theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h
def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)
theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs
theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js
theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)
def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def or01 : Sig := inputs.getD 0 zero ||| inputs.getD 1 zero
theorem or01_table : ∀ r : Row, bit r or01 = (sample r 0 || sample r 1) := by decide +kernel
theorem or01_nonzero : or01 ≠ zero := by decide +kernel

def ImpossibleMono (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k ≤ cap, ¬ Live T k 0 S

theorem imp_mono {T cap S} (h : Impossible T cap S) : ImpossibleMono T cap S :=
  fun k hk => h k 0 hk

theorem rotate_excluded_mono {T n} {ws : List Sig} (hi : ImpossibleMono T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) :
    ImpossibleMono T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

theorem enum_step_mono {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleMono T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    ImpossibleMono T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k _ U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

theorem closeChildMono_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → ImpossibleMono T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    ImpossibleMono T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact imp_mono (scalarPoolCut_sound (pValid _ hp) nd ok)

def evalMoveMono (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let rs := restCov cov.2 (column true a.2) (column true b.2) false ka kb
    if (rs ||| column true z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep false ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

theorem evalMoveMono_sound {raw T r s ws pools links cap a b} {d : Bool} {ka kb : Bool}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → ImpossibleMono T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor (if d then 1 else 0) a b).1)
    (fresh : (movedDecor (if d then 1 else 0) a b).1 ∉ ws.map Prod.fst)
    (test : evalMoveMono (cap,ws.length,ws,preCov ws,pools,links) (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true) :
    ImpossibleMono T (cap-1) (moveFront ws (if d then 1 else 0) a b ka kb).toFinset := by
  let op := if d then 1 else 0
  have hop : (op == 2) = false := by cases d <;> rfl
  let z := movedDecor op a b
  let rest := opKeep false ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    have lk := len_keep ws a b false ka kb ha hb (fun _ => ne)
    simp only [Bool.false_or] at lk
    rw [List.length_cons,List.length_map,lk,Nat.add_comm 1]
  intro k hk h
  have hm : moveFront ws op a b ka kb = child := by simp [moveFront,op,hop,z,rest,child]
  change Live T k 0 (moveFront ws op a b ka kb).toFinset at h
  rw [hm] at h
  have hsz := (live_size h).2
  change child.toFinset.card + 0 ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMoveMono at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_sound h rfl (pair_sep pairs) true (fun _ => rfl)
  have g : (coverage true rest).1 = covered true (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb false ka kb true (fun _ => ne)
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  change column true (pairSig r s z.1) ||| covered true (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (preCov ws).2 (column true a.2) (column true b.2) false ka kb ||| column true z.2) != BitVec.allOnes 768) = false := by
    simpa [getCov] using sep
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k 0 (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChildMono_sound pv lv nd' test k hk h

def testPairMono (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMoveMono ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRowMono (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  bs.all (fun b => testPairMono ctx a b false && testPairMono ctx a b true)
def testAllMono (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRowMono ctx a bs && testAllMono ctx bs

theorem all_binary_mono {ctx ws} (h : testAllMono ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPairMono ctx a b d=true ∨ testPairMono ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllMono,Bool.and_eq_true,testRowMono,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1 b bm).1 | exact (h.1 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1 a haTail).1 | exact (h.1 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPairMono_at {ctx a b d} (h : testPairMono ctx a b d = true) (ka kb : Bool) :
    evalMoveMono ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPairMono,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem node_sound_mono {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → ImpossibleMono T (cap-1) (List.toFinset xs))
    (checks : testAllMono (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    ImpossibleMono T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step_mono nd out
  intro a ha b hb d ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPairMono (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
      ImpossibleMono T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
    exact evalMoveMono_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      (eq ▸ pr) (eq ▸ fr) (testPairMono_at test ka kb)
  rcases all_binary_mono checks haW hbW ab d with hh | hh
  · exact one a b haW hbW ne ka kb pro fresh hh
  · rw [childTwo_swap _ nd]
    exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
      (bin_comm d a.1 b.1 ▸ fresh) hh

theorem linkedSet_sound_mono (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, ImpossibleMono (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    ImpossibleMono (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded_mono (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerifiedMono (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAllMono (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerifiedMono_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, ImpossibleMono (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerifiedMono g k i = true) : ImpossibleMono (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerifiedMono,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound_mono (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound_mono g _ names (prior (by omega)) h

def blockMono (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerifiedMono g k (start+n) && blockMono g k start n
theorem blockMono_at {g k start n} (h : blockMono g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerifiedMono g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [blockMono,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem blockMono_merge {g k start a b} (h : blockMono g k start a=true)
    (h' : blockMono g k (start+a) b=true) : blockMono g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [blockMono,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,blockMono,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTablesMono (g : Forest) (top : Nat) :=
  ∀ k ≤ top, blockMono g k 0 (g.levels k).1 = true

theorem forest_all_mono (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTablesMono g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, ImpossibleMono (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerifiedMono_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact blockMono_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerifiedMono_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact blockMono_at (rows _ hk) i (by omega) (by omega)

theorem root_index_mono {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTablesMono g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : ImpossibleMono (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all_mono g top prior low geom blocks _ le i idx.1

def checkAtMono (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMoveMono c op a b (movedDecor op a b) ka kb

theorem quickAtMono_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (hop : (op == 2) = false) (h : quickAt c i j op ka kb=true) : checkAtMono c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep false ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,by simpa [hop] using closed⟩
  simp only [checkAtMono,evalMoveMono,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAtMono (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAtMono c i j op ka kb

theorem fallbackMono_sound {c i j op ka kb} (hop : (op == 2) = false)
    (h : fallbackAtMono c i j op ka kb=true) : checkAtMono c i j op ka kb=true := by
  simp only [fallbackAtMono,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAtMono_good yes.1 yes.2 hop h
    next => contradiction
  · exact h

def batchMoveMono (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,_,v) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let mask := fullMarks r (takePacked v (packedColumn true a) (packedColumn true b') false ka kb ||| packedColumn true z)
    onMarks (fun c => fallbackAtMono c i j op ka kb) mask xs

theorem batchMoveMono_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) (hop : (op == 2) = false) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMoveMono (makeBatch k n xs) xs i j op ka kb=true) :
    checkAtMono xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAtMono xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] true false ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep false ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAtMono,evalMoveMono,budget,arity,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn true a) (packedColumn true b) false ka kb |||
        packedColumn true (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] true false ka kb op i j = BitVec.allOnes 768
    · apply fallbackMono_sound hop
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

def batchPairMono (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMoveMono b xs i j op
  f false false && f true false && f false true && f true true
def batchRowMono (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  js.all (fun j => batchPairMono b xs i j 0 && batchPairMono b xs i j 1)
def batchRowsMono (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRowMono b xs i js && batchRowsMono b xs js

theorem batchRowsMono_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRowsMono (makeBatch k n xs) xs js=true) :
    testAllMono xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRowsMono,Bool.and_eq_true,batchRowMono,List.all_eq_true] at allRows
    simp only [List.map_cons,testAllMono,testRowMono,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMoveMono_at k n xs
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1 j hj
    have opCheck (d : Bool) (pass : batchPairMono (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPairMono xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      have hop : ((if d then 1 else 0) == 2) = false := by cases d <;> rfl
      simp only [batchPairMono,Bool.and_eq_true] at pass
      simp only [testPairMono,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hop hq budget arity pass.1.1.1,check hi hj' hop hq budget arity pass.1.1.2⟩,
        check hi hj' hop hq budget arity pass.1.2⟩,check hi hj' hop hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatchMono (k n : Nat) (xs : List NodeContext) :=
  batchRowsMono (makeBatch k n xs) xs (List.range n)
theorem runBatchMono_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatchMono k n xs=true) : testAllMono xs[q] xs[q].2.2.1=true := by
  have all := batchRowsMono_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

theorem from_context_mono (g : Forest) (k i : Nat) :
    nodeVerifiedMono g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAllMono (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlockMono {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerifiedMono g k i = true) :
    blockMono g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [blockMono,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def rowCutMono (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRowMono b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCutMono_at {g k start n ar lo len} (h : rowCutMono g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRowMono (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCutMono_merge {g k start n ar lo a b}
    (h : rowCutMono g k start n ar lo a=true) (t : rowCutMono g k start n ar (lo+a) b=true) :
    rowCutMono g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCutMono_at h (lo+j) (by omega) (by omega)
  · exact rowCutMono_at t (lo+j) (by omega) (by omega)

theorem cutsRunMono {g k start n ar} (h : rowCutMono g k start n ar 0 ar=true) :
    runBatchMono k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRowsMono (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRowsMono,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCutMono_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatchMono
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlockMono {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCutMono g k start n ar 0 ar=true) : blockMono g k start n=true := by
  apply makeBlockMono
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context_mono,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatchMono_at hq hb ha hn (cutsRunMono h)

def boxesMono (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCutMono g k start n ar lo num=true
  | d+1 => boxesMono g k start n ar lo (num/2) d ∧ boxesMono g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCutMono {g k start n ar lo num d} (h : boxesMono g k start n ar lo num d) :
    rowCutMono g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCutMono_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cellsMono (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxesMono g k start n ar 0 ar rows
  | d+1 => cellsMono g k start (n/2) ar rows d ∧ cellsMono g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlockMono {g k start n ar rows d} (h : cellsMono g k start n ar rows d) :
    blockMono g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlockMono h.1 (boxesCutMono h.2)
  | succ d ih =>
    have v := blockMono_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def m3935d9 (i : Nat) : Nat := 0x24e020e8d06018100000d6d1ccc7c2bdb8b3aea9a49f9a95908b86817c77726d68635e59544f3d3826140f0a0500aabeae858bd9074ca2155f51d0b17b20e99442abf21a162f641d328865d754cbc5cd52a6510f9a6c1aa6c12a54ca21376ccd54d8254a99443ea9ae6a9ae4a9532887c7361d7360932a6510a8febe8b8c58654ca2152fd6d1718b0ca99442a7ba7a2e316195328854fe4345c62c32a6510aaee9e90abd8654ca21557d7d2155b0ca99442aafafa462b61953288559f5b48c56c32a6510abae9e918ad8654ca21576d2d2315b0ca99442aef21a462b61953288556f5f48552c32a6510ab5eb690aa58654ca21579d3d2154b0ca99442af5a5a42a961953288557d5f48546c32a6510ab7ab690a8d8654ca2157d53d2151b0ca99442afca5a42a36195328855fc4348546c32a6510db3ab2938b12a319a2185fd965f0ab602224430bfb26be156c0444884b7e5f4ac6016088910b7d856b08a0ac1112212f6ccd54d8254910443de9306a9aa490220887bd860d525452044110
def m3935l9 : Packing := (36,6,7,0,4,8,0,m3935d9)
def hashm3935l10 (i : Nat) : Nat := 0x3490923400000000000001c10000341e000349d2084000000000090000000002c06602780e0001816d063c07d0880140000000000000000000006054000f020417e02f41300000000000dc00003c1a30100000000000600c01d324e8110000000000000000000000002c0cb07c000000708a0000000b238c0d00008230000000000080a00000000000000806c0000001896708308b0002c0f825c8120000000600800040700000000000f230405b2240000003819000c18104000050200083
def m3935d10 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x8ffcbc54d8244110a7fd9c60d5244110e7ed936095244110ef6d536095244110c7fd9562d3244110c7fd9856d32441108ffd8c56d3244110e7f98564d2044110ef798554d2044110efd98354d2044110aff98c54d2044110efe9835492044110eff183545204411087fd9c2ad83a65108ff90c2ad83a65108ff51c2ad73a65108ff90c2ad73a651087fd9c2ad82a65108ff51c2ad82a65108ff90c2ad82a65108ff90c2ad52a651087fd9c2ad32a65108ff51c2ad32a65108ff90c2ad32a6510ff615254520a6510c7bda752c83a6510c7eda74ac83a6510c7edac4ac83a6510c7f9a742c83a651087fcac62d73a651087fd8c2ad63a651087fd5c2ad63a651087fd2c2ad63a651087fcac5ed63a651087fcac5ed43a651087fcbc61da2a6510a5fd7c20da2a6510a6fd6c20da2a6510a77d5c20da2a6510a7bd4c20da2a6510a7ed2c20da2a6510a7f51c20da2a6510a7f90c20da2a651097bd4c2ad82a651087fd5c2ad82a651087fd1c2ad82a651087fd0c2ad82a651087fcac62d72a6510c5fdab1ed52a651087fd8c2ad42a651087fd5c2ad42a651087fd3c2ad42a651087fcac62d42a651087fcac5ed42a651087fcac56d42a651087fcac5ad32a651087fcac56d32a651087fcac52d32a651087fcac62d70a651087fd5c2ad988cd1087fd2c2ad988cd10c6fcab1ad988cd1087fd8c2ad978cd1087fd5c2ad978cd1087fd2c2ad978cd1087fd9c2ad878cd1087fcac66d878cd1087fcac66d868cd1087fcac66d768cd1087fd2c2ad958cd1087fd9c2ad658cd1087fcac66d658cd1087fdbc2a5828cd1087fd9c2ad828cd1087fdbc2a5528cd1087fd9c2ad528cd1087fcac66d808cd10aef8ac595608cd10fe7165545608cd10a7f8ac65d208cd10e7e8a9549208cd10ff6152545208cd1087fd5c2ad988891087fd3c2ad9888910c6fcab1ad988891087fcac66d868891087fd8c2ad958891087fd3c2ad958891087fdbc2a5858891087fd9c2ad858891087fcac66d858891087fd9c2ad658891087fcac66d658891087fd9c2ad848891087fcac66d848891087fcac66d548891087fd8c2ad938891087fd5c2ad9388910c7bcab12d938891087fd9c2ad838891087fcac66d838891087fdbc2a4838891087fcac66c8388910c5fca95ec8388910c6fca95ac8388910c77ca956c8388910c7bca952c8388910c7eca94ac8388910c7f4a946c8388910c7f8a942c838891087fd9c2ad638891087fcac66d638891087fdbc2a5538891087fd9c2ad538891087fcac66d538891087fcac66d4388910af74ac5955188910afb4ac61141889108dfd7c2ad808891087fcac66d8088910fe71655456088910feb164505608891087fcac66d308891087fd9c56d3244110e7e9935492044110ef69535492044110ef715156d2044110ef61525452044110 else 0xff6552545208cd10aff8ac601208cd10ff7151541208cd108ffcac62d208cd10df755156d208cd108ffcac56d208cd10aff8ac661208cd10aff8ac65d208cd10aff8ac61d208cd10b7f99c215208cd10bdf97c215208cd10bef96c215208cd10bfd93c215208cd10bff11c215208cd10e7f8a95d5208cd10ff7165545208cd10ffe152545208cd10ffe12c545208cd10dff1515ad208cd10bef96c16d208cd10bff11c16d208cd10c7fcab16d9888910c7fd862ad9588910a7fd3c2a58588910a7fcac6618588910c7fd962ad85889108ffd3c2ad8588910a7fcac66d8588910a7fcac66165889108ffd8c2ad65889108ffd3c2ad65889108ffcac62d6588910b5fd7c2159488910b6fd6c2159488910b7dd3c2159488910b7ed2c2159488910b7f90c2159488910a7fcac6618488910a7fcac6558488910c7fd962ad84889108ffd5c2ad8488910a7fcac6616488910a7fcac65564889108ffcac62d6488910a7fcac6615488910afbcac61154889108ffcac62d54889108ffcac5ad5488910a7fcac6159388910c7fd852ad9388910c7fd652ad9388910c7fd962ad83889108ffd5c2ad8388910d6fd955ac8388910c7fca956c8388910d77d9556c8388910d77d9c56c8388910df751c56c8388910d7bd9552c8388910d7ed954ac8388910d7f99542c8388910c7fd982ad6388910c7fd952ad6388910c7fd942ad63889108ffd8c2ad63889108ffd5c2ad63889108ffcac62d6388910a7fcac6615388910e77ca96155388910af7cac6155388910c7fd962ad5388910c7fd952ad5388910c7fd942ad53889108ffd8c2ad5388910c7fca962d53889108ffcac62d53889108ffcac5ad53889108ffcac5ad43889108ffcac56d4388910fe75865955188910aff4ac60d5188910bef56c20d5188910bf755c20d5188910bfb54c20d5188910bfe52c20d5188910bff10c20d5188910aff4ac58d5188910aff4ac54d5188910bfb54c22d5188910afbcac6114188910aff4ac6154188910bdf57c2154188910bef56c2154188910bfd53c2154188910bfe52c2154188910bff10c2154188910aff4ac5954188910aff4ac58d4188910aff4ac54d4188910a7fcac64d8088910c7fd962ad8088910c7fd932ad80889108ffd5c2ad80889108ffd3c2ad8088910a7fcac66d8088910aff8ac60160889108ffcac62d6088910aff8ac6156088910aff8ac6116088910aff8ac60d6088910aff8ac54d6088910fef1655456088910fef1645456088910fef1635456088910fef1655056088910ffb1845056088910fef1635056088910a7fcac6615088910a7fcac64d5088910ff71516015088910aff8ac60150889108ffcac62d50889108ffcac5ad5088910a7fcac6613088910aff8ac60130889108ffcac62d30889108ffcac5ad30889108ffcac56d3088910) else (if i<3 then 0x8ffd2c2ad978cd10a7fd8c2ad978cd10c7fd5c2ad978cd10a7fd5c2a5878cd10c7fd952ad878cd108ffd5c2ad878cd108ffd2c2ad878cd108ffcac66d878cd1097fd5c26d878cd10a7fcac661968cd10a7fcac65d968cd10a7fcac61d968cd108ffcac66d868cd10a7fcac661768cd108ffcac66d768cd108ffcac62d768cd10a7fcac661958cd1097fcbc661958cd10a7fcac65d958cd10c7fd762ad958cd10a7fcac5ad958cd10a7fcac4ad958cd10a7fd2c2a5758cd108ffcac66d758cd10a7fcac661658cd10a7fcac65d658cd10cefd862ad658cd10cf7d852ad658cd108ffd8c2ad658cd108ffd2c2ad658cd108ffcac66d658cd108ffcac5ed658cd10a7fcac661928cd10a7fcac65d928cd108ffcac62c928cd1097fd9c56c928cd10a7fd5c2a5828cd10abfcac61d828cd10c7fd972ad828cd10c7fd962ad828cd10c7fd952ad828cd108ffd5c2ad828cd108ffcac66d828cd1097fd9c56c828cd10d7f99542c828cd10a7fd5c2a5728cd108ffcac66d728cd108ffcac62d728cd10aefcac595628cd108ffcac66d628cd10d6fd6526d628cd1097fd5c26d628cd108ffcac62d628cd10a7fd8c2a5528cd10a7fcac661528cd10e77ca95d5528cd10e7eca9609528cd10e7eca95c9528cd10c7fd982ad528cd10c7fd962ad528cd10cfed822ad528cd108ffd8c2ad528cd108ffcac66d528cd108ffcac5ad528cd10a7fcac65d818cd10a7fcac661718cd108ffcac62d718cd10a7fcac661518cd10a7fcac65d518cd10aff4ac661518cd10aff4ac65d518cd10aff4ac61d518cd10f77598595518cd10f77597595518cd10fe7586595518cd10fe7576595518cd10bf755c249518cd10aff4ac609518cd10b7f59c209518cd10bf755c209518cd10bff10c209518cd10fe7565589518cd10b7f49c589518cd10f77598549518cd10ff6582549518cd10ff6572549518cd10fd747c549518cd10bf756c549518cd10aff4ac62d518cd10b7f59c22d518cd10bdf57c22d518cd10aff4ac4ad518cd10bef56c0ad518cd10bff10c0ad518cd10a7fcac65d808cd10c7fd972ad808cd10c7fd962ad808cd108ffd5c2ad808cd108ffd2c2ad808cd108ffcac46d808cd10a7fcac661708cd108ffd8c2ad708cd108ffd5c2ad708cd108ffcac62d708cd10a7fcac661608cd10a7fcac65d608cd10fe7565545608cd10aff8ac601608cd10aff8ac5c1608cd108ffcac62d608cd108ffcac5ed608cd10aff8ac661608cd10e7f8ac661608cd10aff8ac65d608cd10aff8ac61d608cd10aff8ac609608cd10aff8ac549608cd10bff11c149608cd10f7f198545608cd10fef165545608cd10ff7152545608cd10fef16c545608cd10ff7151581508cd108ffcac5ed508cd10df75515ad508cd108ffcac5ad508cd10a7fcac661208cd10a7fcac65d208cd10 else 0xf3ed8760952a6510e7eda460952a6510e7eda360952a6510f3ed8360952a6510f76d5360952a6510f76c5c60952a6510e7eda85c952a6510e7eda65c952a6510e7eda45c952a6510e7eda35c952a6510f5ed735c952a6510f76d535c952a6510b7ed8c5c952a651097fd3c2ad52a6510f5ed821ed52a6510d5fc7b52d52a6510d5fc7b4ed52a6510f75d530ed52a6510d7dd3b0ed52a6510b5fd7c20c52a6510b7bd4c20c52a6510b7ed2c20c52a651097fdbc20c52a6510d7bd8652c52a6510d7bd8352c52a6510d7bd6352c52a6510d7dd834ec52a651097fd8c4ec52a6510c7fd872ad42a6510c7fd852ad42a6510b7bd4c2a132a6510b7ed2c2a132a651097fdbc2a132a651097fcbc61d32a6510b6fd6c29532a651097fdbc29532a651097fcbc61532a651097fcbc61132a6510e7dda85cd32a6510f5dd875cd32a6510e7dda65cd32a6510e7dda55cd32a6510f5dd745cd32a651097fdbc60932a6510f3ed8760932a6510e7eda560932a6510f3ed8360932a6510f7cd7360932a651097fdbc54932a6510f7cd7350932a651097fd8c2ad32a6510c7fda562d32a6510a7fcac5ad32a6510c7fda856d32a6510c7fda656d32a6510d7dd7356d32a6510d7ed8256d32a651097fd8c56d32a6510d5fc7c56d32a651097fdbc21432a6510d3fd8662c32a6510d3fd8562c32a6510d3fc8562c32a6510d3fd6562c32a6510d3fd6c62c32a6510d3fd5c62c32a6510d3fc5c62c32a6510d5fd865ec32a6510d5fd855ec32a6510d5fc855ec32a6510d5fd655ec32a6510d6fd855ac32a6510d77d8556c32a6510d77c8556c32a6510d77d6556c32a651097fd8c56c32a6510d77d8656c32a6510d77d8c56c32a6510d77c8c56c32a6510d77d6c56c32a6510d7bd8652c32a6510d7bd8552c32a6510d7bc8552c32a6510d7bd6552c32a6510d7f58646c32a6510d7f58546c32a6510d7f48546c32a6510d7f56546c32a6510d7f98642c32a6510d7f98542c32a651097fcbc5cd80a6510f37d8554d80a651097fcbc54d80a651097fcbc54980a651097fcbc4c980a6510b5fd7c0ed80a6510b6fd6c0ed80a6510b6fd6c20d70a6510b77d5c20d70a6510b7bd4c20d70a6510b7ed2c20d70a6510f5dd7354d70a6510f57d7554970a6510f5dd734c970a6510b5fd7c20d50a6510b6fd6c20d50a6510b77d5c20d50a6510b7bd4c20d50a6510b7ed2c20d50a6510b7f51c20d50a6510f5f9735c150a6510f75d8554d30a6510f75d5354930a6510b5fd7c20d20a6510b6fd6c20d20a6510b77d5c20d20a6510b7bd4c20d20a6510b7ed2c20d20a6510f76d5354920a6510f5f9735c120a65108ffd5c2ad988cd108ffd2c2ad988cd10cefcab1ad988cd108ffcac5ec988cd10a7fcac661978cd10c7fd982ad978cd108ffd8c2ad978cd108ffd5c2ad978cd10)) else (if i<6 then (if i<5 then 0xe45788a09124220e437886090a4210e41788209024200e3f787d48f741eae3ce87888ef41dae3ae874e8e801c9638586f08dac1aee35686928d0819d633386588c9418d631386188c1417d62f385d88b7c168e2ca85868ad815762a785408a58147628184f489cc134626184a8892812162358456888410ce20c83f287d40f6e1dd83a687300e261bd836686b00d0e1978320860c0bde17182d4858c0ac614e828e84e8099612b82488468084e0f981d28364068e0c1816882b40516095811c821c03fe07280d08184026e03d806c80a4010e01a802c800097fcbc65d83a6510d7bd9752c83a6510d7ed974ac83a6510d7ed9c4ac83a6510dfe90c4ac83a651097fcbc66173a6510b5fd7c20d92a6510b6fd6c20d92a6510b77d5c20d92a6510b7bd4c20d92a6510b7ed2c20d92a651097fcbc65d82a6510afbd4c2ad82a6510aff51c2ad82a65108ffd3c2ad82a651097fcbc65d52a65108ffd3c2ad52a651097fcbc66132a651097fcbc65d32a65108ffd8c2ad32a6510bdf97c20d20a6510bef96c20d20a6510bf795c20d20a6510bfb94c20d20a6510bfe92c20d20a6510ff695354920a6510a7fcac5ed83a6510d5fc2c5ec83a6510d7ecac4ac83a6510d7ed7c4ac83a6510d7ed5c4ac83a6510d7ec5c4ac83a6510d7ed1c4ac83a6510d7ed0c4ac83a6510b7bd4c2a173a651097fcbc61d63a6510c7fd872ad63a6510c7fd852ad63a6510a7fd5c20da2a6510b5fd7c20ca2a6510b6fd6c20ca2a6510b77d5c20ca2a6510b7bd4c20ca2a6510b7ed2c20ca2a651097fdbc20ca2a6510d3fd8362ca2a6510d7bd8352ca2a651097fd8c4eca2a6510f1fd875d982a6510e3fd8769582a6510b6fd6c29582a6510b7ed2c29582a651097fdbc29582a6510e3fd8769182a6510b3fd8c28d82a6510b6fd6c28d82a6510b7ed2c28d82a651097fdbc28d82a6510e3fda560d82a6510f1fd875cd82a6510b3fd8c5cd82a651097fcbc5cd82a6510f3dd8358d82a651097fcbc58d82a6510f3dd8354d82a651097fcbc54d82a6510b7bd4c2ad82a651097fd3c2ad82a6510a7fcac56d82a6510b6fd6c16d82a6510b7bd4c16d82a6510b7dc3c52d82a6510b5fd7c0ed82a6510b6fd6c0ed82a6510b77d5c0ed82a6510b7bd4c0ed82a6510b7f51c0ed82a6510b7f90c0ed82a651097fdbc14c82a6510d77d5356c82a6510d7dd534ec82a651097fd5c4ec82a6510b6fd6c20d72a6510b77d5c20d72a6510b7bd4c20d72a6510b7ed2c20d72a6510b7f90c20d72a6510f5dd7354d72a6510f3ed8760962a6510f3ed8360962a6510b6fd6c28d52a6510b77d5c28d52a651097fdbc28d52a651097fcbc60d52a6510b5fd7c20d52a6510b7bd4c20d52a6510b7ed2c20d52a6510b7f90c20d52a651097fdbc20d52a651097fcbc5cd52a651097fcbc58d52a6510 else 0x400701f1031d2f00f8c063f1410c1a4800e03e200701f136401e88adda1a66048c80ce1b3018300701f174701d7e2fcc0bb81e9baa57d3f1448c0f4a00e03e2ec5e98ef405424640140ba6014840681eb6804e980724c803f01f3c3b087270dda1acc33c863f0c0a172c2c885570a3a138c2548487089a104c1ec839f06ca0cac17882b704fa090c10481e7038a050c09080e7012a00abff87fb6fef9fcabf6c7e86fc69f84bef87dcefb59f62bea87d2ef9e9f2ebe407c5ef849f00bde47ba6f709ed2bd947aeef599eb0bd507a36f429e70bcdc7936f1f9e30bc44784ef029df0bbc4774eee29db6bb507666ec59d82baf475aeeae9d4eba8074c6e919d20ba30743ee809cf8b9d4736ee639cb2b9307226e3a9c60b8a4713ee239c3eb87870e6e1b9c2eb84c7076e0a9c0cb8147006df99be4b7ac6f1eddf9bbcb7446e1edb69b52b6886cd6d939b1eb6206beed739ad8b5a06b06d599aa4b52c6a1ed399a6ab4c46966d289a48b47468ded179a2cb4546856d0699feb3e0679ecec99c4b37866ceccf9990b2c86556ca39932b2486456c8398f2b1c86356c6098b2b1486256c409872b0c86156c239832b0486056c0397f2afc85f56be397b2af485e56bc39778aee05d6eba6973eae605c86b899704adec5b9eb6f96d6ad9c5afeb5896a2ad285a16b3b9668acc0595eb24963aac585876b079606abf057beaf395deabac571eadc95b0ab50567eacb958eab0055c6aae954eaa8c54dea979526aa30543ea8094f8a9d4536ea6994caa97852cea55949ca9285216a3b946ea8c05146a21943aa8585076a0a9406a7fc4fbe9f693dea7a04f069d693a4a72c4e369bf9376a6d04d669a89342a6684c9698b9308a5f44bc697492d4a58c4b0e95a92aca53c4a3e9409272a4c84956923923ea460489e90f921ca434485e9079206a40848068fc91f0a3d0477e8eb91c8a38c46f68da91aca348466e8c99184a2ec45b68af9150a29044ce892911ca21c43fe87890e2a1b4434686490c0a17042be853909ea12c42368429076a0d0417e82b904ea08c410e81a9026a03c403e8008ffe9fe03fb67ef8fd09f903efe7db8fa89f343e467c18f7a9ee43d8e7ad8f4c9e7c3cbe7908f129e083bd67738ed89da03aee7568e9e9d203a067398e649cac391e71c8e2a9c3838366ff8df09bb837366df8db09b44364e6c28d709ac4354e6a28d369a5034666828cf699d033666658cbc995c32666458c7c98dc31966318c54988c30de6148c1a98182ff65f78be097a42f265da8ba097182dde5b18b5a96a42d0e59d8b3296542c8658c8b1096102bfe57b8aee95c02b5e5648aba95582a8e54d8a9295142a0653c8a6a94ac293651f8a36945c289650b8a0893f427964eb89c8937426c64d1899a9318257e4a28930925c247e48588f691dc237e46888c8918c230) else (if i<7 then 0x100b04008016268e083e027ee28c0101344baa100100414bbc9d080064e85d1da0029f40edb067d033ba19f40edb076d83b6c1db60edb076d822efb6c2e8e0c216db04110376c19d50800064e8400202820d00f476800b40819c400040161000100585a04d1c29c80ce404050205a1ca202d0e5100a040b439440a4113909d4f47080b42272670202710c101388608029a18407b05a20130631005003895d40fc400202c2686081f81eedb0c01010c408602c200100b160e7430b073a185839d0c2028686120e16c0807c074403e03a201f86710020160807c074403e03a200112300b180f80e8903048c4002016200100b10330140801c198407e07af6c357503f10770160804fa184054c0820138921009f430b8003a9c006027d0c2007a861009c49080f60f8507c07a202852110008025430c0100b04002016200a01314c704000207e20010b11014290880043b84014c08200100b10008058800402c40020162e003f41077072a78034007c01a001d43ca9e00d001e54f006800f2a54008887a0019a90891896890303b301d1a0e8d074683a3411320ecc076603b30102400d111e040340a04059018200180c1581050f028781db60edb076d8216fb6c203a3a9e861d5486aa40e84282114108a08401c034404801a202d06d103680606c8c00402c407a478200d026100b0400402c4478100100b105b84c801e6f858d470009fadba601300bc80c3953d30300008168816bb141e86009d8a0163c860d477010aaa78085c04100002890416c6e00066270203d1380019880ac8e81506e0407a270003313800198818c90416c6e04068270003314020268a7d19640906faa3a13e80484629fc59f402420230120811c07c40990740e6302b07210050140811c07c404a03e204703d10ec8239fa012130a7f14fd00908063f8a7e80484c29fc53f40242614fe29fa0121002809047bff8a0860484a0401f10158390801407c401a050204701f1035b208290c1a4094405604a2027025109181280f8c09407c404a03e217705623a01f203201d82d00f9009407c408e03e2fb6051a8e072200a039881e41cc40c80d2201407aaa0180a014080daa380f41cc80c80d2206406910acb470348c0500a05be801551c0b6404f68e0691833014080daa3810c150808a0f4050305f0430541832034885de6d9a801109d0df8ab6c05a2efd4060520a0e0290bb7fedbe600b4148b59007e03e301303d101f81e8801c07c406c0f803e301301f103e11d00f8c0fea1816c600e03e2df4016a8605b200380f880fea1816c600e03e200701f101b03e00f8ff141e407c601402e20e8fc5043069200380f8804c07c400e03e29f40d90241835cefb6401f812140aa77db200fc090a0d73bed9007e048506b9df2c803f024290200f881ae77db200fc090a031f8a0860d2 else (if i<8 then 0x416c36020961b0104015408200aa0411020681000440154082a0400110055020802a81054080022d00c0416806020b4030105a018082d00c04168006f1422ee24608ef0c78a50250b020e809810169f146c082ee246324419260410c93020811a810427d8742ee317783e04718bb8158150d0a402b010604a1025081284094204a138e025100084007010400380821773dd14060402a8104014100aa041406040282015408200a080550209030209c808020c70e74e4105dc227d4742ee3000200089c8ef8919402a8105408002200700a1015916880ac8b444330c3438301306110098308804c18440260c2201300a100980088649030530c19860800c060b0137205809b902c04dc816022e4090101184017708bb8681013040981a0404c10020ec0b0100c076478098b1b8a3c04458dc538e220202b08010004714600839d390313ea3a1010b4285a1000085a142d0a16850b4278a104ea86810004400e060205ba1c1023018080c020c04177123d8626020bb891ec3130105dc48d6188272324818246403d80c1005406080f60304014100180c1012ae440f0e0180960786015408200a0805502080106484015408200aa0410020c90a87064848c681813c50a0606f142246100180c102638200000ce44060c48c3408002202b60415db041681f0538a076c0837c508ef84010004714600e08c20471391230030013a940c381ec060802a0304247018014303d80c101ec060802a0304247018014303d80c10054060848c02811c607b018200a80c10054060848e030028607b018200180c101ec060802a0304247018014303d80c101ec060802a0304247018014303d80c101ec060800e0304247018006303d80c101dc06080ae030408c08e202b089c8238158f0100ac43258082ddfc0416efe020b7170105b8b8082dc5c0416e2e020a0b420ac180c0ed4e020b6a70104b538082da9c0416d4e0208035010505b008202b08158761b0105b0d8082d86c0416c36020961b0104056180c804154706a382d1c1bc5080080789edb714551c1a8e0d4706a38351c104722d1000807880100b2a386008016268e0896f470a7d0378a100f9751347065dc13c4d1c10010041000807886a4378a103782d134705a38208e418268e083c837880a81e44be81177db610020218801002c4d1c100100410008060af14200320821a9083591688001ea9220f803f1000807880103140586d1c100fe8e100a0411c8b44d1c1004016103c89c89a3820f2a70212de8e107c00b081b01ec40de0a2205240c1216850b42e6c0df1b038d803f1000100584d1c1004016100183c881f013c4002008200f06f10078018b401a3853aa10039d510bb847542000340021dc10004e4327011290b6f85f14215e02c20694846a421dc1d2908138409c20020c6200186712fa040 else 0xbc5a0413e2b0209f158104324c08270060410235020b61b0105b0d8082d86c))))
def m3935l10 : Packing := (613,5,7,6,4,15,0,m3935d10)
def hashm3935l11 (i : Nat) : Nat := (if i<1 then 0x28a4ec27a00000000000000905248090209480000e06380000000000000b03784130b26240000000000000000038173000000000b061b01270065d0207708254023b00700000000000000005d4000010395009fd089e80db00000000900002821800003c0c5a043c000000002400bd062f809b7068d4085a02a3021c109900000000bbc194305c400003034201660000241f6d03980000605be011c00001c0b1d04fc00005074141df0000000008011d008de08f000007067680e29001e00d9327f00000f2648c1be606b3418aa0042c0884275800fc00003c0c460687c2267025ec12cc070c0000427c80000e095b41fd20288c1648039c0000508de6479d001bc1932003dc11e83013c20ec084b404900000000000003819f00000000000003009d0000000003069d8119d01080000893940000000000000e04e0000000002802b804d04200e05b881883072901d3a2010c1a0b087dc244c0192c21e2026440af208db808600003c184471cc80e8f04934026a0128000010354000000001c0d80091901b10000302032020c00004004880da405a5c0e4606400000a00a141ad703d0c1dc201000000000024a050000009cc000000000d272ae87470747c2601005c00000292c00000000100270000041a800001019190178c0c8f042300f9c0960000010630000080569c0965321640a1da1d78225000008cc5000000000002b9c1e85098cc0aa6025241b080562008430655c0dfb07b58079a076f68b4d21d3802c804f5c0d77018c806c133200000f27c241e090439c8717057ec0d6471e50159b094441c4a07080000a022649e0000000000008d10131421980000601cbc0fe827ac81927215a04fd5098800000000381d6901cc0000203d9022e0000240b9aa32c000000000423d000000000807cc000000000000090859803100001818900003c997a05520a28106980000b04f88038907a4023aa06f70067000030024b03340000b0808c04d20601c07ea32e00000f046980b0728abc01be023341852044f81180045d013cc029f025900924000000003c9dff05dec1d9e03840093006a6407c000024151a01f5e882e2659c0611140fc255005f60032000004241b06e0c05d4042a40a3202d3c1c9000028081d084000005048fc239d06e541f1201484146031c04100004020202070100011b080702040204030907030002150528030f0005090209050904050d0c19030a000d0a07030203030a01010200010814020004270100070301110001011200070902100d03060a0600290a2b230a00093c21201c01090b02140606010104050719040b140520111401020006040701020007160000001c051b150014060f000115020514130102000004000116170d06010303131b4c011c000400150500010200040200020205000505030011083b else (if i<2 then 0x1ae821adc06dc058381ab92721c1c6f082ac1251034b004c6055e009259294c021203080247800e809c900352403f504362426e05a981d7907a94859e01bdca5cf05780000500378243c066701cd2058bc2570023ed478402920238400140000f03fcc17ea022800eea101000001041000004059744fad06938126028f4c1e750784000000001c00cb04064046807638a049088249ade094000001042e425e000018016908cc0000e038181f4702e1c022702cdc0b2000000000f1417013b006d00000000000000826a68a3e0000340c0601d4000080458000060865814c000020254d280c423f5004c40510000140ada07efca3c803b40000000010071d0934000060111001f8273c419e802f7c01d00003022a205ca025b62926c01e00000c0c600000000000000802d30750281c406cc9479827600000000024865d27aa80fa00002c1bce0138000000000000000003424cc038e00bf905fd8235608060a12d068980ea000004245f28ee0163d0832014b000024122c06abc167b05ee0863e088c812e0000341f9306638261c050d805b70856025ab28cba8b5b084f8020b01dd898ef13ed4140607bec1b282844807a2090800000000000000000140588018200419017e89c7008c9014fc01e109a40082d0001526360179c2678000040377c048d01d849e160798405cc0721c176171d1809cd28ce40fd828c580b6b28d20095d07e8c183005a2c18da020380b70000280d10000000006061c0000e200b40ca00003c1ccb014f099de070302302295341290030d8214d090180fb00001405740261c15d3006a24ba90875498c204bc00004277141152097c8875b00d0906a1093a8150401d0000080788817cd0659806a628bf81da00002c24a00000000000000413900003400e805238128104dc0000a047c40f7b04240000000000000703380000906ec0000403c7c08e208f80000000010a0d6048000000000149ba00000c14500003025c2071601819041c0000a04b60a29d070701e4c00f6c0dcd08a3406e503b2c0f00029400007263f803c3067340b5c3307c21a00000000000000000000000000082669804500000814a000030c88000034069d071d824b70534c9f8401a30c80902a54008401400000b010e8000206df4a4260794012a0000000bc003a780eb0000100c7b294100250000041330000000001022c00004040000009016681cf7050800002094c0000000000000000000110e06fc0000000000000000000000000034102800cf8248404ac00f3803c8c03be27d1850280158c19b907e34082a293eca30605b1c019f086c00008055801def51d4c9dd400dc80bb4078d018f607c3c9998040cca63a07c9c22b00002c09e904c8c112000a641ce00003017830450000070044c19a4a2bc000000000ccc30000201ee903beccc400 else 0x3c0a6000000000d26540000f01ee4062508bc89c17028349e5000004070f0333c153c05d38111c01fc0000300620a62e0820c1afb093f81d200431c15210556c2060000000005051f816d00000000000001417ad083d0030f02e80000000000000f00e40000000000000e01ac0000f0885825d0000181b51058480f5605722478b056f01f7f02f800cf000000000f05ac00001026b4229a20040000921e90002d0835000a6012e82056216c801500003803e200508136204840000427bc004f007fb01ba307760a5e8051241ffa07b3822c10246811d208c74cca50890411b926da49f300001802a5000d80c100002443a00000000000002c1d5a08100000102b200365933cc004407d6c106d04154170308ec0000000000000327c40000a060800008085c00000000000006015500f8204d44211301694054b00d749e7c07f2013aa072c01414032d0087501980000102ad485a100bc0000506d94065907ae49ffd088bc9f9608b601a539345ca5df0324c14e1264000004034c4))
def m3935d11 (i : Nat) : Nat := (if i<6 then (if i<3 then (if i<1 then 0x60a33442bfecd90519a217fe42c828cd10cff952b94668857fc9b58a334433fe54aa519a213ff2ad528cd10aff936a94668857fd9b14a33442f7eb58a519a217fd46c528cd10bff216294668877f59854633443bfacbaa319a21fdd595518cd10feeaa4a8c66884ffcab60233442bfecdb0119a213ff2ad708cd10eff330b0466887ef96558233443ff8a8ac119a21fdd545508cd10affb36a84668877f99748233443ff4a924119a21ffc545208cd10bff2d690466884ffcab662224433fe55b3111221dbf1ad9888910affb36c34448867fca9616224427fe55b0b112215ff66d8588910affb3642c44885dfd7b21622442f7eb590b112217ef52c8588910bfba7642c44885fed2b21622442ffa8d90b112217fe42c85889109ff956b2c448857fd9b596224427fe55b09112215ff66d8488910affb36b24448857fd9b552224427fe55b27112219ff2ad9388910ef7896c9c44884ffcab60e22442bfecdb07112219ff2a48388910affb3641c44885dfd7b20e22442f7eb5907112217df56c8388910bf7a9641c44885fed2b20e22442ffa8d907112217fe42c83889109ff956b1c448857fd9b58e224433fe54aa7112213ff2ad5388910affb36a9c448857fd9b14e22442ffa8d8a7112215ff66d4388910efeb30a8c44887f756554622443fdac228311221fed5914188910efeb26a0c44885ff55b506224427fe55a63112213ff2ad8088910affb36c04448877f99858222443f7cb2ac111221fbe5916088910fdf2c6b0444887ff15158222443ff8a0ac111221fdd5455088910affb36a84448857fd9b4c2224433fecc326882219ff62d9344110cffab6c9a208867fd2b64d104427fecdb06882219ff6619244110cffb2ac92208867fd93649104433fec5b24882219ff4ed9244110cffb2ac12208867fd93609104433fecdb04882213ff66d8244110cffb26a9220886fed82549104433fecdaa4882213ff66d52441109ffb3699220884ffd8b4c9104427feada6488221bfe6612044110dff32a90220886ff985481104437fcc9a4088221bfe60d2044110dff2a690220886ff98b481104437fcada4088221bfe4ed2044110adfad651d328855fd7b20e99442bdea59074ca215fb4ac83a6510aff21641d328847fcab58e99442bdea59454ca211ff2ad82a6510af7a96295328847fcab50a994429fec58654ca2157f5ec32a6510adfad61953288577d5b0ca99442bdea58654ca215fd46c32a6510aff216195328847fd8b2a6334423fead95319a211ff4aca98cd108ff956cc4668847fcab65e334423fe55b2b19a219fe2a5208cd108ffb1654c448847fd5b2a6224423fe9d953112211ff2ad98889108ff956cac448847fcab64e224423fecdb06882211ff66d82441108ffb36992208867f993481104437f4a924088221bfc5452044110 else (if i<2 then 0x21bff56d32441109ff956c1d328857fd9b60e99442bfecd9074ca2177f5ec83a6510bf7a9641d32885fed2b20e99442ffc859074ca213ff2ad73a6510affb36b9d32884ffcab60a99442bfecdb054ca215ff66d72a65109ff956a95328857fd9b54a994427fe55a654ca215ff66d32a6510eff32e905328877f99348299443ff4a92414ca21ffc54520a6510affb1651d328857fd7b28e99442bfead9474ca215ff4aca3a6510cffb4ec1d328867fda360e994433fed5b074ca215ff2ad83a6510cffb4e41d328857fd7b20e99442bfe959074ca215ff42c83a6510cffb50b9d328875fd875ce994433fed32e74ca21d7f5d173a6510cffb46b9d328857fcab5ce99442bfec5ae74ca21df760d63a6510affaf6b1d328877bd8450e99442bfec5a874ca215ff5ed43a6510cffb0ed15328867fd8368a994433fe41b454ca219ff5cda2a6510affb16515328857fd5b28a99442bfe9d9454ca219ff6a182a6510e7fb0ec15328867fda560a994433fed23054ca219ff68d82a6510e7fb06c15328867fda260a994433fed5b054ca215ff2ad82a6510affab6415328857fd4b20a99442bfe9d9054ca219ff6a172a6510cffb4cb95328867fda55ca994433fed22e54ca219ff68d72a6510ebfae6b95328857fd8b5ca99443b7ebb2c54ca21dbf58d62a6510efdb04b15328857fd8b58a99442bfebdac54ca219ff69152a6510cffb46a95328867fda254a99443bf6c12a54ca21dfb5c952a6510cffb56a95328857fcab54a99442bfebdaa54ca21d7f1ed52a6510affa96295328857fd3b14a99443bdeba2854ca21def55142a6510ef7a86a15328857fd8b50a99442bfebda854ca215ff56d42a6510cffb50995328867fda64ca994433fed2a654ca219ff68d32a6510efbae6995328867fda24ca99443bf6c12654ca21dfb50932a6510cffb56995328857fcab4ca99442bfec5a654ca215ff5ed32a6510affad6995328857fd5b4ca99442bfea5a654ca215ff62c32a6510affad6195328857fd5b0ca994439fec2b014ca21d7f5d570a6510ebfae6b85328857fd8b5c299443bfcc02a14ca21dfe5c150a6510affb16a85328857fd7b54299443beea9a614ca21dfe60130a6510affb16985328857fd7b4c299442bfeada614ca21dfb54920a6510eff2e0905328877f93048299442bfec5a414ca215ff5ed20a6510affab6905328857fd3b482994427fe55b3119a219ff2ad988cd10edf8d6cc466884ffcab65e334433fe55b2f19a219ff2a5878cd109ff956c3c668857fd9b61e33442bfe4db0f19a215ff66d868cd10affb36bb4668857fd9b21633442efebd90b19a217bf5ac858cd10bfba7642c66885fed2b21633442ffa8d90b19a217fe42c858cd10cff952bac66884ffcab59633442bfecdacb19a215ff26d658cd10cff952c1466884ffcab else 0xe90466887ff99648233443ffcc324119a21ffe5d9208cd10fff32a90466887ff89548233443ffc42a4119a21ffe5d5208cd10fff2ca90466887ff98148233443ffca8a4119a21ffe26d208cd10fff11690466887ff85b48233443bfe2db3111221dff0ed9888910effb0ccac448877fc8b65622443bfe1db2b11221dff6618588910effb2cc2c448877fd9561622443bfecdb0b112217ff52c8588910bffa7642c44885ffd0b21622443bfecc2cb11221fbf6196588910effb2ab2c44887f7d8559622442ffec5acb11221dff6199488910effb0aca4448877fc8565222443bfeb2b2911221dff6618488910effb2cc24448877fd9561222443bfecc2c911221dff6556488910ff7b08b2444885ffd8b59222443bfecc2a911221dff6595488910effb2aaa444887fbd8455222442ffec5aa9112217ff5ad5488910effb0ac9c448877fd6564e22443bfeb232711221dff5519388910eff8b6c9c448877fd9520e22442ffead907112217ff42c8388910effb30b1c44887efd8658e22443bfecaac711221dff6516388910fdfac8b1c44885ffd8b58e22443bfecc2a711221dff6595388910effb2aa9c44887f7d8554e22443bfeca2a711221fdf5515388910dff956a9c44885ffd8b54e22442ffeb5aa711221dff6605388910effb2c29c44885ffd8b14e22442ffeb58a7112217ff42c5388910effb30a1c448877fd9650e22443bfecaa8711221fef6114388910bffb16a1c44885ffd6b50e22442ffeada8711221ffd6195188910ffeb0aa8c44887ff56554622443ffac22a311221ffd5915188910ffeaa8a8c44887ff58354622443ffa41aa311221ffd58d5188910ffeaa6a8c44887ff54354622443ffa45aa311221ffd0ed5188910ff7b08a0c44887ff58650622443ffac2a8311221ffd2154188910ffeacaa0c44887ff58350622443ffab1a8311221ffd54d4188910effb2cc04448877fd9560222443dfec2b0111221dff64d8088910ffeaa2c04448877fd9b60222443f7eb2ac111221fbf58d6088910fff300b0444885ffd8b58222443ffcc2ac111221ffe6116088910fff2a8b0444887ff98358222443ffca9ac111221ffe14d6088910fff286b04448877fd9854222443bfecb2a111221dff64d5088910ffeaa2a8444887ff98054222443ffcb02a111221dff66d5088910bffb16a8444885ffd6b54222443bfecc26111221dff6593088910effb2a98444887fdd534c222443ffaa8a6111221ffe6013088910fff2c098444885ffd8b4c222442ffeb5a61112217ff56d3088910dffb36c1a20886ffd83649104437fecab0488221bff64d8244110dffaa6c1220886ffd9b609104437feadb0488221bff4ed8244110dffb26a9220886ffd83549104437fecdaa488221bff4ed5244110dffb0a99220886ffd9b4c9104437fec5a64882)) else (if i<4 then 0x3443bfe15b2b19a217ff62c958cd10bffa564ac66885ffd9b21633442ffe9590b19a217ff46c858cd10bffa1642c66887dfd875d633443bfecb2eb19a217ff66d758cd10effb30b2c668877fd9759633443f7ec32cb19a21fbf5d9658cd10bffb36b2c66885ffd7b59633443bfecc32519a21dff261928cd10effb2ec94668877fd9664a33443bfecab2519a21dff255928cd10effb30494668877fd9524a33442ffec592519a217ff56c928cd10effb2ec1466887bfd8760a33443bfecb30519a21dff655828cd10dff956c1466885ffd9b60a33443bfeca90519a217ff66c828cd10bffab641466885ffd0b20a33443bfecc2e519a21dff659728cd10effb2ab9466885ffd9b5ca33442ffec5ae519a21dff661628cd10effb2eb1466887efd7658a33443bfecaac519a21fbf595628cd10ffdb04b1466885ffd9b58a33442ffec5ac519a217ff5ed628cd10effb30a94668877fd9654a33443fbebaaa519a21ffb609528cd10ffdae4a9466885ffd9b54a33442ffebdaa519a21f7f1ed528cd10bffad6a94668877fd9614a33442ffecd8a519a217ff62c528cd10bffad629466885ffd0b14a33443bfecbb0319a21dff655818cd10f7fb04c0c668877fd985c633443efec3ae319a21dff655718cd10fbfae4b8c66885ffd8b5c633443bfecc2a319a21dff65d518cd10fefaa4a8c66887ff58154633443ffab8aa319a21dff66d518cd10bffaf6a8c66887ff59854633443ffa4c2a319a21ffd65d518cd10ffeb0ea8c66887ff59654633443ffac32a319a21ffd5d9518cd10ffeacaa8c66887ff59254633443ffa492a319a21ffd609518cd10ffe904a8c66887ff57254633443ffab12a319a21ffd549518cd10ffe936a8c66887ff58b54633443ffa45aa319a21ffd5ed518cd10ffead6a8c66887ff52b54633443ffa15aa319a21ffd42d518cd10effb2ec04668877fd9660233443dfec0b0119a21ffd545808cd10bffa36c04668877fd985c233443bfecb2e119a21f7f5d5708cd10fbfae2b8466887ff5515c233442ffec5ae119a21dff661608cd10effb2eb04668877fd9558233443f7eb2ac119a21ffd545608cd10fff300b0466887ff97058233442ffec5ac119a217ff5ed608cd10fff330b0466887ff99758233443ffcc3ac119a21ffe655608cd10fff2eab0466887ff99258233443ffcc12c119a21ffe5c9608cd10fff2a4b0466887ff85258233443ffaa8aa119a21ffe581508cd10bffaf6a8466885ffd6b54233442ffe8daa119a21dff661208cd10effb2e904668877fd9648233443bfecaa4119a21ffb549208cd10ffeaa290466887ff98048233443ffcb824119a21ffe581208cd10fff2a090466885ffd8b48233442ffebda4119a217ff5ad208cd10bffab690466887ff99848233443ffc4c24119a21ffe65d208cd10fff3 else (if i<5 then 0xf54d82a6510effa86c15328877fcab60a99443bfebdb054ca21dff5ad82a6510effab6c15328877fc5b60a99443bfea5b054ca21dff4ed82a6510eff876c15328877fd1b60a99443bfe85b054ca21dff54c82a6510eff8a6415328877fd4320a99443bfec32e54ca21dff61172a6510effb06b95328877fc835ca99443bfeb1ae54ca21dff54d72a6510effa86b95328877fd8758a99443bfebaac54ca21dff60d62a6510effae6b15328877fd5358a99443bfe29ac54ca21dff60962a6510effae8a95328877fca354a99443bfec1aa54ca21dff20d52a6510effae6a95328877fd6354a99443bfea1aa54ca21dff60952a6510effac4a95328877fcab54a99443bfebdaa54ca21dff52d52a6510effa76a95328877fc3b54a99443bfe85aa54ca21dff60c52a6510eff906295328877fd6314a99443bfea18a54ca21dff61d42a6510effaeaa15328877fd8350a99443bfeb9a854ca21dff54d42a6510effb04a15328877fd5250a99443bfe542654ca21dff61d32a6510effb0c995328877fd764ca99443bfe52a654ca21dff61532a6510effaea995328877fd654ca99443bfec22654ca21dff5d132a6510effaa8995328877fd834ca99443bfeb9a654ca21dff58d32a6510effaa6995328877fd824ca99443bfeb12654ca21dff54932a6510effa84995328877fcab4ca99443bfec5a654ca21dff22d32a6510effaf6995328877fd6b4ca99443bfeada654ca21dff16d32a6510effa96995328877fd1b4ca99443bfe85a654ca21dff61832a6510effb0a195328877fc850ca99443bfeb28654ca21dff61d80a6510effb0ac05328877fd8360299443bfeb9b014ca21dff54d80a6510effb04c05328877fd7260299443bfea93014ca21dff4c980a6510eff876c05328877fd855c299443bfec1ae14ca21dff20d70a6510effaa6b85328877fd825c299443bfea92e14ca21dff4c970a6510effb0ea85328877fd8354299443bfe41aa14ca21dff5cd50a6510effb04a85328877fd7254299443bfe992a14ca21dff61d30a6510effb0a985328877fd834c299443bfeb9a614ca21dff54d30a6510effb04985328877fd724c299443bfea92614ca21dff4c930a6510effb0e905328877fd8548299443bfec1a414ca21dff20d20a6510effae6905328877fd53482994437fe55b3119a21fbf1ad988cd10eff856cc466885ffd7b26233442ffead93119a217ff4ac988cd10effb30cbc668877fc9865e334437fe55b2f19a21dff22d978cd10dff956c3c66885ffd9b61e33443bfecc32d19a21dff65d968cd10effb0ecb4668877fd9761a33442ffecdb0d19a21dff661768cd10fbfb0ebb466885ffd9b5da33442ffec5aed19a21dff661958cd10eff930cac668877fd9765633443bfecb32b19a21dff5d9958cd10effad6cac668877fd2b6563 else 0xc3539d5340531a52e952b85292524b522551ff51d9517c50d250ac507050294fd74f904f5f4f444efd4eb64e7a4e284dcb4d844d324ce04ca44c524c004bcf4b7d4b4c4aef4a9d4a4b4a0f49654929490348dd488b485a47fd47c1477a473346ec46b04669460c45d04589454244e5449e443643ce438742e842754244421e41b6416f413e40d6409a4053400c3faf3f683f163ec43e723e203dd93d713d1f3c753c233be73bc13aeb3a8e3a47397c392a38cd389c383f382437fe37b73770374a372436dd3696367b3655361935dd3596357b3555352f34f334b73470343433cc3385333332e1329a326931eb31a43173312c30fb30a93062301b2fd42f822f3b2ee92ea22e502e092da12d7b2ce72ca02c642c332bf72b8f2b3d2af62a832a2629c92961291a28d32876280e279b2754270226bb2674262225db2568252124da2467242023d92392234022ee22b2224a21f821a62154210220bb206920171fc51f731f2c1ee51e881e361dfa1dbe1d981d721d361ce41c921c611c0f1bd31b811b2f1add1a8b1a3919e71995194e19071873183717e517a9176d171b16be1677163015de15971566151f14c2147b143413f813bc136a132312dc128a124e121d11ec11bb1195116f113e110d10dc10b61090101d0fd60fa50f7f0f170ec50e940e580e320dbf0d570d260d0b0cb90c880c410bef0bc90b8d0b510ae90a810a2409c7095f090d08bb0869082207e6079f0758071106ca0683063c05ea05980551051504ad045b041403d8039c036b032f02bc027501f7019a013200eb00af005d0000eff876cbd328877fd9760e99443bfec9b074ca21dff66d83a6510effb2e41d32885ffd2b20e99443bfecc2e74ca21dff64d73a6510effb0ec95328877fd8364a99443bfe41b254ca21dff5cd92a6510effb30c15328877fd9760a99443dfec3b054ca21dff65582a6510effb26c1532887bfd8360a994437fe55b054ca21dff66d82a6510effb2ea95328877fd9354a99443ff6c12a54ca21ffb5c952a6510effb36a95328877fd984ca99443bfecba654ca21dff65532a6510effb2699532887fdd734ca99443ff6c12654ca21dff66d32a6510bffb1699532885ffd5b4ca99443ffcc3a414ca21ffe61520a6510fff30690532887ff88348299443ffcb9a414ca21ffe54d20a6510effae8c1d328877fcab60e99443bfebdb074ca21dff52d83a6510effa56c1d328877fc2b60e99443bfe85b074ca21dff2a173a6510effb06b9d328877fc8b5ce99443bfec3ac74ca21dff60d63a6510effae6b1d328877fc5b58e99443bfe15ac74ca21dff61d43a6510effb06515328877fc8328a99443bfec3b054ca21dff5d982a6510eff94ac15328877fd8460a99443bfeba3054ca21dff28d82a6510effb06c15328877fd7360a99443bfeb1b054ca21df))) else (if i<9 then (if i<7 then 0x2bad05acd4acc4ac9eac83ac68ac37ac11abebabafab89ab58ab27aae0aabaaa94aa63aa48aa17a9f1a9c0a9a5a974a943a928a8f7a8c6a8a0a86fa83ea82ea813a7f8a7d2a796a770a755a719a6fea6e3a6b2a681a650a61fa5e3a5b2a581a545a514a4e3a4a7a476a445a414a3e3a3b2a38ca35ba340a304a2c8a297a250a214a1d8a1b2a197a171a14ba125a0e9a0b8a087a0359ff99fc89f8c9f509f2a9f049ed39ea29e669e4b9e0f9dde9dad9d929d619d309cf49cc39c929c569c1a9bf49bc39b879b569b309af49ac39ab39a989a679a4c9a319a0b99e599ca99af99899958992798e098a49873984d982797f697d097aa9784975e9738971296e196b096749638960795d695a595749543951294e194b0948a9459942893f793d193ab93859354932e92fd92d792a692759244921391e291b191a191869155912f910990d890b2908c907c905690308fff8fd98fb38f778f468f2b8f058edf8ec48e938e628e478e218df08dca8daf8d898d6e8d3d8d0c8cf18cb58c9a8c7f8c598c288c0d8be78bb68b908b6a8b4f8b1e8ae28ac78aac8a7b8a3f8a1989e889c28991896b893a891488d8889c88768850882a880f87de87c3878787568725870a86ce869d866c8646861585e485b385988567853684fa84b3848d845c8441841b83df83ae83728336831b82df82ae82938257821081d481a381728141811b80df80a3807d804c7ffa7fc97fae7f7d7f417f267f007eda7ebf7e997e737e4d7e1c7df67dc57d9f7d797d537d2d7d127cd67cb07c8a7c597c1d7bec7bd17ba07b7a7b5f7b2e7b137ae27ab17a8b7a657a3f79f879d279ac797b7955793a791478ee78c878a2787c7856783b781577ef77c977a3778877577731771676f076ca76a47689764d7632760175c57594756e7532750c74db749f746e743d740c73d073947379735e7338731d72ec72c67295726f723e721871e771ab717a715f7139711370e270bc7096707b706070246ff36fb76f916f606f246f096ecd6ea76e816e506e1f6dee6db26d766d456d146ce36cb26c8c6c666c356c0f6bd36ba26b716b356b046ad36a976a506a1f69d869b26976692f690968d868b26881685b682a67f967c8678c675b673566f966c866a26671663565f965c8658c655b6540650464d364a264716435640463d363976366633562f962d362b8627c623561f961d361a2617c6156613060ff60e460be60986067603660105ff55fc45f9e5f6d5f3c5f215efb5ee05ec55eaa5e845e5e5e225dfc5dcb5d8f5d5e5d225cfc5cc05ca55c745c435c285bf75bd15b955b6f5b335b025ad15a955a6f5a335a1859dc59cc59b15996597059555945591458f958bd588c585b581f57f957e957ce57a857825751572056c35671561455ee55c85581555b552a54ee54d3548c54715440541a53f453 else (if i<8 then 0x50c090348f54b1ad901e40b945b8031dded800ac81d07d524d894918d901e40f9c35df41a00909aa7001293bfe606803d3e00c087d0d00d92ea9e53803021a03e8340f8007505ac08680fa0d03ea9e53803021a03e8340faa794e00c08680fa0d03ea9e53800eff981a00f4faa794a04044680fa0d03f291337d3cc0015900f8faa494918e01178349aef86f05a03d64241306f1be2dc4c8031dde600a001f6c0105aac86918b53b201e8692edf1ca6a7db02d1a007cfb7fe282d3400f4baa49491909a1e4b2a7471297bfe62ea83d3e8ec00309fa3b6f31b201ea354bdf2826636412336a97e9f14e012307a6d521a7e2fb6b3048c0f9f6fbd507a48e8d01f30220180901e903b0b70dab203380c36a9d1c4a4efa15f309781ea354e8ef31178bb83d368e074ea4a09770bc6d52e80a0ec82ee5d520e9d01770bc5553a381d5f4f30f541e9f54df4f8ae80a083d36dfd1de636402d07a6dbfa38afa1505a9780f9f54929a349783496506865e816c9adb4c0790b64553a636e86926980f216c7a192085b1e8e018bd02d924302d01816c9bd15000c0b645e810c2a0d506f40b630cd37d1680a00fa3830e1a5ab8e1418754e1ad8b8e0349b5b6a94821489a391d05b1edf9520581202f0cd8e30d4c848611b0b7c0b61ac71354fb7f62a410a44dbfb174723a0b65dbe9042d8c00adf91c02c026a91cb3231c61a5001dbf2380205a0db8e30d4c84e8e9900e81a1016834168e056aa6066989918e0fb7e430410b64d52006064c85418e0db7c15aa98198e1504c83852c700d07b7f476c5c700d0bb7f62e98c700d0a0c40903ef8a158c717709907138a427702e00124239a03e809138a703702e01f14d01f40488c5204b81700f8a680fa0244629c0df178130034015cfa024484901c1581f84c0820f8e1841781e06648ce443a38490b60642b878068194f97fdb1322467540618248690ac1040f1714861390578d000c365fc5211caf1a00186c52720bb95e340030d97c179c82bc680061b2fe29390578d000c365fc52720af1a00186cbf8a4e40432bc680061fe282d0921f24707b0827093f140603a9400b4c1243d83a940030a0dc14851f8a1279c07c0f2a81217c1bf00e705643caa0384906e1ec3caa005a6092a380607b082501c0b437cc808250d61066402d205f05a18e6404128370520640703fe357d01e828590a06e0641f8265900b4c17c1b829033edbcc02507a1e4122c85cdfd53a1b6287b9418e02da037ea9d1d80b4c4c80693d02a2754edf9912831c05b36df5413231c05b28d80560334c6385aa0a0fa395482dd6d06a6403d0b68b3c1b39bb375b34fb308b2ccb2a6b275b244b213b1d7b1a6b180b15ab134b103b0d2b0acb086b060b02faff3afcdafa7af76af50af2aaef9aed3aeadae87ae61ae30adf4adceada8ad82ad51ad else 0x738e34721377d2fa2945a0392085238494eb8a6108122ee184919dff8a63b9c71a0c818df97f14812f8a48d208253a2945a18d20852285647407c619224a75c530840780408e4e4d492300601c00fc5e71c6832e419e5f008140efbd52bd68023a3149a9b1d720bba41365f8920aa1080f00877c2393924600c039c5003ce38d05ac832cbf8a4ef9a9b90904129f149393527203095e34003104f00617707a4cbe77c9c9c805e578d000c443a068208f0702b8f2f9d5390e3a2084731a931c11e0643a068605a0101a0de280406830d463be2c0c8740d0c77cc71d58190e81a1a02034118e0080d0618be2c0c8820d0a138efc0c8820d0a0c4effc58191041a1a0e05710040180d0603002034186131df161d03429c808e1361d034282f3be638e2c3a068602477fe2c4106850de050238b715221be2df45409028a1b807c5e701ccda189e68ee01f159c07338631be2deeafb6b90a80e18d6fa39f6ca80ac98248474821ec803c5b803b8a19000dd5be9720022a05936253c039c1490e66d1c4e83d824268620dc03e29390e66e005dcacea02686026394169f43aa3a0fa187282d3e8754741b430e505a7d0ea8e836861ca0b4fa1d51d061b03940b02d3e8754741f430e505a7d0ea8e8368602c394169f43aa3a0e1f024a8ebaa11d209b83047be9f14612a00887d0c41b805d52efa80c190a4813be9f174710c28409121ed1d0691864e520105b8a9007ed8008e1b9011c1faa06ea91dda80061f41a06d527d0060e81a0509211d2087b2538d1c1e4af0242847b8a1241802d0f6059472414f5f16e00fdb001540360fb7c3268e274560121b6f86426e394d4ea0019ce0990d0506f0184f0d4ea02ee4c86820066df0dfed8d4ea025a34100336f86f273ed8d4ea025a3413a1be2fb605a4a4399b6ffb605a757501593686252309fa7c505aedb50236f95925240bdb01605a363502794f060ec11c5bfc50061e947067568642bf16113380e66ebe2deeafb6b8aa80269f54e86f8b6db501773686274f54db6a02ee6d0c0b4bbbd52756db501f6fe86f8bed896c2236dfd0c190098ee42a0b4eab38844adbe723db7982b2148d0136ffb6553a80291b6f959018408807b6b9005816ea056a9f8a4e8bbb38050615223bcc2c80180f4c04d54a8ef30b201e9b54e8e2840feefa5e03e7d53a389490ebbf1780f9ec7064054b212094388b713200fdb001050b2075274713621d6a6fa6c803e7d1c394169dff303601e9f470661cbe60169f41b07d1c19872f9805a7d06c1c3313205a48cfa0d830e2028397cc02d3e8360fa3833016f300b4fa0d83e8e1ca0b4eff981b00f4fa38330e5f300b4fa0d83899be8308142c80886d1c43ad4df48bc07cdca45bfb6a341c80fac81d08d524d894ddff8a4841e9f54df424250426976f95fbaa4841e954302407a3)) else (if i<11 then (if i<10 then 0xc29392830f1d0119b129d0c0b406941693a478305a05406d1ad0c5d0c4c846a74302d018405a0f49d23c212dd0c201503202686203d2748f06cdb4342221c07cb088a0a3c1c2221da181681f2c04553a1a801154c22d0d46880101118ed0c030a088061411c040150328d6862941478280802a0651ad0c5482100303048b405081221c01430de19848e82185026c501641ca02c409015e98018130b011020d8d8a4016029020302204d8a0b06c00b2c04408248687023940589020d001630148e82d8c3100a48216c9c08910240b64d53a1b817003be11cc764146a9d0df17817003e8090faa4497c5e05c00ef98ec8286008102d8c248470b6309c77cc302b48207cc08d1d05b186131c8e82d90ef98e3908e81a151d05b102f3be714c723a0b6647416c4048efa410b640180101a0c060040683a0015a02034200a0740d060c40904705602be2862882878a11c268c2b0318740d081300943a03e40c4965208d1485f45bf151d06930144381f461591d01f1df44b20906139e43d50927d0d03c508e84938a40204735200f8170000e007e2812c087d0d03cbb001048309d7212087c08e531c754e43f4b4011cc13aeadc845b6813a8473e5f39011ceaa4104a6bab7151d069204703e2009756e43f4b4011cd8a703062f8a5de2099eabc8b405dc239714e067bff14d004104a7c53818d49860d1f1620825465f3bef55e444104a681cf7c293d5391104239e1484785a04ee40628827853010293f404858be139ea9c887411c2a1c1781231c0ac309c8882705e7220e044206105e77c15812391104e01ae423a0e640ea133db1d9e341483d9c84047b1c83835bd50c2904e11d14a2df8a1851d2233a290c21ed0e0792c490eb8a5108612461880518ef8a61b9c71a026051e8a51685f482148a1b120852185647407c783891f9805e720fa00c381e01807c1293149a9246049d01c83e8031083aeaa41b9011ca83aeaf984ea57823992fa0e3aa906e4047325fbabed910dc808e60f775520dc808e5cbe757db3a039011cd8380218e7bf757cc15e08e8c1cf54e40412ee5c52e3ae418e0825dcd8a707061f8a5de209b14e0e0f06a4c75c82ef1051839eaf982ee578239823dc54be1c4187c505e88520a423dc54bff141838e05e1ed20a6efa5f3900a52085230494eb838179770c20aceffc5353ce38d06c0d6ecbf838039d80ac130eaf38e34721491435a410a4408c8e80f8f2fe0e00877cc7058f3057823a72fe0e05fedbcc03031320180940f932f9df27248fdb79802475406272fbd508272012972f98675372020825365fc52682e404104a6c526a4c73df24772220825465f3bf071ea95e04a6cbe77ce2ba9b91104129c23a297bff140907c482708e8a516fc50249d5209eef84705497dea812482745201916fc54741a4d97c1080f098764e8 else 0x5d1cf2074034703c18d8d1c75464b5110816d2976da3980147712d44630afa38ea8e94844601a3880b694b0078ba38a09c81386446425a8884524afd00d1c4671a389d0f47104106d0dfa3a80109d68e104d66da3ae2902693ad1d7149013471d5184bd1c4106137471d51c04292408d4dc5d1c6b6da389d0edb68e274305a4eb475b621b60864e87a389d089d68ea703275a38ee8e9c68e27432754e3470c9d68eb6c3275a3adb0f471dd102dd1d6d86f57475b61e8e0196d86a1b471f41e8e2bc2552f17475b620232724f064b6110816e8e6703808757470c9d338d1c325ba384cd809906019a38a030680806338d1c4e880300990605ba38b01154e8ea004019a3a800e8130230da3806140204a1a030184eb47338250260461b4702d290202d01347120210209434080f40b68e2744808408e2816d1c5009409db186d1c5d1c410401068083de8e3903d1c4e840e9fa68e6704074f74680e81186d1c0b484000b10418231ca0b40b11ea8521a0307410f4713920044ec5db473382e8e6040b40b10860921027d1c430609c860231942014ea74311c703fd0c307afd3430c96e86112dd0c21d4028061f4d0c54744e8bae8620ea05a0280668628ea66da18687343132246405a050710e5d0c525a3604508bb84307b0f0ba181d1f4182d1850f065df4343ab6c42084e61d68623f407a50743120e07101447343160e119d0cea405142183d2828f0819cfa686b30403f660a0e86207203e5a34310bbdc0878303f703430cbb9c0d0c5049a18a09231b3626407e196862c3203fa18a09016d98d0c4c88072061a9d0c48cb070826862464273a18a09232600a305a8336862e00a305081e843478604ba19e012320254644c80fe86634602fa18120c6c813d0d638051594e002083a805686320424424876d81f9778784d0c0e8fa0c1edb607f0f08484a0c3c19c0247a18a09082139875a188cd82d00a0de49528e80513ad0c501403016e86260031da1872a50e11c243a18a87019686634450c050588f0000a209a188410efa3c4744e4a04d9b686b1c028a0281fd8ed0c4014394168e2d0c5d0c0f89c83f212d124204ccd80fe86b40528207f435a0202603fa1ad01074686038680907074104d0c48ca4e7431412464209a1a0e12324a9c01401fa6862e001d5a18d493001a9d0c30892a491872d0cc68b2a743141181f26425bf2a700500d0c5953802800d971c028d2a70050076da18b803431a91ca9741a198d12948d925a3245a18968e066862383246fd34351a2686a342246028990ddb686a343247a187451a23b6247a1a8d1154e86a3434784e840b4af80d0da4809a1a800c0695fa35a188aa43680da0040ce8f040f41e13a183c27422750f044ea1e0a1d17787832ee5061e0c1913907b0f0a0961d17787835530e89cc3c213907a0fdc743) else (if i<12 then 0xa024124089a89049020477aa446e9089c84347458241a10e1232412438f4c91920923226448d0e1602012408188c314079d078a346e0481f23a2404024810c3031281231c18403901e93c47430240bce418e01850180780fa1c220408070ca20c6810c719220073a020248e84f140385a1a0445a648609d0e088aa04100132487060f49ca3ab0c480802a0658621772468b60602b014607a8e82193981853be119e2c0421df0570106004efc041ddf08d0102392efc04056300277e020c268468083bbe158168eef8018083bbf010008c26dc50570108006e284d808408f71426801808508e136e282b05a500371426c04204db8b0102b1000dc509b01090b6d4846808485b6a400c0425a971c0060212d484685b01090b6d4801808409a11a020e16da9003010848ac7046838424563815c1c200131d07061189141c182b31d070763891001838409a11a0e0c9158e0ad0708004c741c1d8608d0320212065860570109032c30018084b0c03400c04258608d0302392065860570108a3824eb47080a13c70da388413473c51904d1c4b460588268e218476d717470c31904d1c351c10c6f7f470d4707b0c834086d8d4e8e213ad1d6d864eadb68e1c3a2745d5e2e8e287926fa3afa109d68e1177d1d77470eb471dd193ad1c28744109ce8e202d76c193471096e8e102dd1cf1460b49d3b6d1c426ef77470c16e8e102d78ba3864b7470875064d1c4109a3886016208425ba3840b46c0e5d1c058a4b47108968e21047d1c75468e89bdd5d1c4409a38410ca117718432b3a38a1101d68e3e83075a38ee8c9d68e143a2084e74710063b602605747174710c100c1a020184e9db68e200c05a04c0ae8e2b00d1c43074080a13ad1c4a044b7470d6f864d1c41084134712d1cdfd1c198a4903de8e390390c8e89d68e2ea59bf21809866d1c51c2059470d021b6d1c3029a3ac30f4710c100c1dc363471086092105166c1f3475c82a3a07fa3ae41028813d1d7208813470823904b8a05b4714bbc3cd1c1e481e4a4e8e2bc4074774680c09c3c0f3a3880e8c3139d1c48740f3471f4213ad1c220805a1d68e243a02c57b471254b36d1c5603e1654dc54744e81fe8e31d50a43406b7e549a9d1c4d1c7544810e2e8e18471b04100b68e292fd1c0c00b111d10438a05b47161181426fa3ac3174710c100c1cba3875064280cd1c4f09c9086092147629257e9c68e2c7605a190afd38d1c6808a183b68ea0458974e2e2e8e2404097a3a81122582dd1d7149010a58151c042934e08068e282d2521be9c68e282d3aba38605a8168e05a40ec6a49c68e05ac00379c0204bd1c75484b7470a020573aba388012803b6353a38ba388208021d5d1c32b3a38ea8f4713a1500d1cfd06f74eae8e18c2353a387400d4e8e0184205a38820d6fa86a01a3883bb4738619d else 0x5c58080046f1400a04180131c8706004f12411847006f16c7204002650dc0b80001c0857be1191d0c2302431c870961a02046818481961800c04200381961a020012c0cb0c11a0210ef80a474378a028060e06702e00345aea405204202471c0290e1206702e003014810058c3080a474378a0ad0204c2024438e38060562c2de05c007c0b8004c19d80148101811ef80a474378a029020d16ba90148108028d000c1c0ce05c00663b8170019920148707c0b80001c08438bc0b80001c08508d402020c15d008083003402020c05500003010940026404182ba01010616c91bd3438440810c4f14078cf421c100f0ca2408639061e220013c48706810230471c0409c810315c5284939c11c61ecfa43a2ee407c5dc3143a243707c139e298e87468744f9168e1d13e27230f648ed041c200180820070100082520640f6f1461e11d3dd2ee401481048643086743840b648de9a1c200a40820c261831064206540893823903283f2ee38081950206e2065246e810e1102040387b107847420c2f14038c15a043be8b5d4950c869438300e194404d021863be184a1851d0830a041404015032c31116b8e819618807c91a1cb0c4272fd2e423a221909848ee421c2c0409811ee412025c809811c88dc1f939b908e8b01026047b904247721d021c203d78a5dcaf43a295e272f561d121e03d2ef0e880f49cc3a2bc48780f49cc3a20432730e9c7101e93c87433b248d0e3d322040982809162e2a044c45809162e2a0471c549cf14239d922378b17141f93947468b171491ba0438505e184d49c800e507a5791d0c1820413c500e7606f142e21c1bc500e168604d02186060760a76015830408480802a0658624042ee48c0540cb0c0ace0f51d586273030a07c91a1cb0c483248de281f838583216c91bd583850d207c918c3481f24633401a40f923201e03e0320e100f1c801807e0e140520414124081ede28472c12272fd11d12091397ba8e8802902))))
def m3935l11 : Packing := (840,4,7,10,4,16,0,m3935d11)
def hashm3935l12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xcd5022c9c000000000823c500200000000000000c0be400007098202e5a0858000092bb800000000340970000381ac000004d4f00000000000002832100000000000000c0ba000000000000000000520f0000010c400000e01b000002011c0000303ec000082cc94064000008b0a000000000000008aca000000000000000000403c8000030694826a00000000000003c1ed000000000964d00000000000624f03f4404972d1fc66a000000000a0a34000032abe01f810c788185000000000a09740000e00f40000000000000000000000508a8000000000000000000000000000000000000000000000000092c6800003038c0000d244f8342d0394000000000000000002002b306608a9bc18a24832000034ae000000000000003c24e0000000000088800000000145d30000380f5e50aa033f301dc83130000248b900000000000000000082c8ac2710000000000000181ba00001c2da30900000000000000090ac80000b049c000000000000000000c04f0000202aca2cb44ad4c02300000c074000000000308dae0553803f0000282d9c065c0000000000000000000000000000000f07cbc02300000000000002420100000000000000000000001807c000000000c08e8000090b240000a0467c193b06d44a8d10628c02e00002008bd0b8e012000003c0d700000000000001c2440000000002012a8083109b4000000000417d3031f811f000000000000014b30b2414c12e0000305e40000000000000000005012308bd0000341b652ab5400700000000000000000000000000030b7f41c9000000000a2c6d000c43538007182bc0013b00002018400000c03900000cb42396e800000000341db200080000000000000000000000c08280000000000000000000000000020af3802cfc0eab096440c840b840000802f00000000000000b02380000607540000202a581c1708bc000000000000000001012a00000c25e002200000000014258000028d6642d0481e700af900fa206f4000000000004e60137297f0000000000d0202050f020e00040000010700060c04000b01000300010400020401000000000001000000010e0100000005000301040108090000000101060004060105030111051c02060006020001000001061b080100020002100302010201030600000600050104070112050701030c070100040005000201090200080001000300030003000100020301030203040a0300000509040003040009000d00000d00000200040002060009040700010401030100040401070005010300010400010c040403000002030000000000040b040201010202000000020000030b08030110020000010000000b0f05000403000004000100060300000001040002060401100003030e010403000000000000050209000200000300010102 else (if i<2 then 0x4e007c000000001082100001028a70bf1c17800002c19500000000000001833e9037a827f00001c1460000142cd4037c000050658000000000000000000c0c900003812fd070982a74400d027e000024220a06cc4a94d0248000002083c2ca70c6c0000760bc00006042d02e4d09ce8009305700000406d0000000003ac2e5018d82aa22aac008490035429810160000030340000000c640000000000c6e00002864300000000000000000000001c23492328c2eb60062c054000000000800d3407ab0356c06d220ae03028069c000032b36015bb068742a300000090000000cd54f055800000000200152085c0000a031401ff8019e02539245283330000248bb000000000824240000000000000e24a40000a0956cb38e07280000e23a4000000001805200003866be963880da001ad8ac600000e95a000000000000000000b00900000000000000302ac0000a07dc000000002813000000000000000000000000413ae060ecb10000010111a1774000000002c2a80000281e40000000000000140b020cdf40cc0000301f0ca0a0000042ce400000000000004010cc2290043e001eea5d9430d00000493b90ae0418700001826100000000000000000042b580000108948345000000000717898227f0cb0caa2f0c28000000000000052c5c0000e06a0000af242ec33c401d0000000000000000001423f90730000000003816d207e8000000000000000001c2750000180d3f2c53414fc91e7405f0000000000000000000000000002074c00000052aac2d000010aeab0aa40000908e40000000000000000018116000018032d0acc00000000140530000041afa3548000000000000000000000000c99c294000010aece20b00000000000000802794323000000000509180000e077800000000000003082c00005058a4ae9000000000000000000000000000a0904000072cec0035900ef42760000000008091d429e0000000007075282c49084c0000c03bd0af2918f40000007a80000000000000000034057b09e8008500003402ac06e142a1107ec000000000000000001c8e78031000004087c00000000000000000000000000000000000000000000000000000000000000240625083082d6d095c431660c6801f3201b900dd000000000d02340000d0c1641cb00003c8bf000034a9a00000c2ad00000000000001822c000000105707d40000801cc0000000000000c2b434314a0c800000000034ac700003c17bf04a7420370addc34030428dd42000000000000000000000000000000000000000000000d175c00000000302880000141b1000000000000030ad200000000040638000070884000000000411020a6c0000696c4000042c540000d207c0000000000000917da829fe366a02e020cb4000000000000000000000000bb800000000 else 0x20005802c8000000001420f000000000000000000000000000201f7009a000004ac5000000000c0564021a00000000000000000000000c2e6a011000008045400005067d01bf0000081c700000000000000000000000e59f00001c2b600002821900003c1ee00000000000000000020cf40000000000000000000000000000000804b000000000182ceb050e02d80000240b8709d1257b000038d5130c1e80e000000000000000000000000000000000c1690000000006020b810c000000000000000000f36fc0000c2af182fa40bd080a0605e7c05600000c8df83110000030cec0189000000000000008ab090d1c000000003425bd04dc816b000008a86000010938309dc0000631a9015160650000040598cb450000209239011400009047400000000188ed92bb5428fb05dc0000000000000d2b980000000000000000000000000000000f209c01f452cc7c8e4506b54096d00808a89919a5429220b7102c7004f3005b7044fc142006330095e0140000072b9c0000a0ca4000080c13c82870930c8d6823ca80332098840100000082ba000028aa53073800000a50ac8bed2456421e3055f05e500000000000000000000000000000000000000000000000000000082c1cc081000000000000030093d0794c8e60000141a6b02f80000000000000809970148c0924882d0000342f800003801cb08374245395b6c2260000301a220ac5c270209ec000000348000000c3cc1fdf0c9c0000000000000000030300109bc0000000010174e092000000000082f110cd5401300001821ce06e5c83400363400300002000b00000000000002829000000000080c1b0a90425040000000000000000000000000000000305e8000012b4c4026000000000d0c04c0a700000000002b64000000a5f0a92e0489020780c5c0000a0118c215f029481fc000018131702b40000d06a800007081782e8531e0000000003c25400000432200000029a00002c14052c2d4006205820341a057ca4784027000000000182d3000000000b2a740000e0bb0a9460000000000000340b1a0ce6810800000000040b540000e099841612068c0000f0c0d80370000040b9864d5ca8be07218236a0a44000000002424a000000000f0438c212707d842a00000000000000081e6d028800000000083440000341e9d0c7400000000342b0705480000670b800004206ecad5c006c8001600c502f6000000000b040f88b3000000000e0aed014d0000002283080340aed2c340000006ef41ef92a640000403c40000a36a2824f000000000000000000b0427c1c0b03f2cadb4178502c8403d8428400000c0eb82354c92120b9fcb36000000000000000000000000000000000000102dec11a208f7009f70644000030ba80000000020b240000000000000000000000080e)) else (if i<4 then 0xa0a3b0149000000000a2ab00000b96f38268000000000c36540000102900000000000000000000000196c9413e0000182ffa022701cd6019842793077000003241f8165000010230000000000000034309c06480000000000000000014186000000000a0893c1734008a8025d08ac0126c01c340e1520bb42f0c090fcadae9687c0143010981e2d0c7fc8d700000000000000000000000c32800000000000003c2fd00000000000000000000001004000000000000003832b0000302db62c648218a2cb3008052c7388ffd0674017010b3102d790968000010494c0e8706ac00005041c0000b20cc0000c05bb4134a094301da000000000908d40000000000000306f8c1f100002c2c50000000000000148c2000000000502400000c36cc0000000000000a0aac000000000000000000000010a2c00000000301a4102a380b500000c18b00003c1b000000892d000014d550000165af00001cb3f00000000000b0c000000000000000000698a000000000000008b0c50ce94296d00e1c15300002807e0000000000000141e300844000000002003a000000000e2a2000000000000000000280ca00003431100001434630460000000001c18832314000000000c2e9000000000000004af40000385e30000000000000203360000280dc000000000336a8000000000429c80448000000000c14b40bbd8172409ac0b180000000000000000000000000000000000000000000000000000000000140aa0000000000000342ae0000000000000000000000081e8000000000102d8000030a040000901db01ec000000000000038114d0144c2d44070d818fd032f030eb005ac000d05f18b2eb073ec2f5403ce42c0000000000b04a00000000000000000000000000008331c01e00000407800000000000000000000000003c00000909b9011b000000000a2ce8000000000000080b18000000000000000003655d0000000005099c0000000000000e03b40000000000000104fc000000000000000001c180000000000000000000000000000701c800000000000000000000008030c0000000000000000038091000000000c0a6703340006502bc8355a00e6900f8000000000000090c90000000000405d60471c15ad058f80c2b0a9a40acc2335825cd310c000040958000000003030b00000449d000000000323cc00000000380cfe05420282000000000c23a91038000000000000000000709480000f0784810000003423bb076600ce0000180e9101a30b0f00000000000001820900001020290a880000c08cc000040ad4021000002414700000000022468000000000000000000000000000808ab06800000000000000d086cd82da23100000000000000f0bf80000d06040000000000000700a40000000000000000000000000 else (if i<5 then 0x92b00000000000000c164f0cb80000e01e40000922e0a96a809c9c231000000000f06bbc289000000000e06a40000b0157414c404ca823250408014ec09f740a3404780000702758801f04340000e2a298325a01a49c2800001e5b900000000010a30000000000000000002c06a0066c000000002c8de000000000b20aa8da3000000190000004264a0a94000000003c8e5000012565000000000c04d400000000000000000000001017a682eb050500d1000000000e0c200000d057880c10000000000000102bfb025208fe00000cd4b00000c278a96ec00000000040e240262401ab09a600ecb250a01d68a19ac13900002403c00001cdbab01ec000000000000010664000000001c8dc0000000000000042cf000000000601fcc1dd40a18000000003c214e0abc0000603e70928000000000000000000000000000000000000000000000e0c5442d200001cabf0000000000000000003005e40cd00000000000000000000000c28300001c33000002009920bb4000000001cac200002492f1016acb20f04f4090a202ecc12d0000102c182a4f40d98041048048055788370000000000000000000000000000000241d2000000000b2c8d80860000048eed06680000c0a54000000000caf5000000000d36058332c04d8c1d1900c2416ad0164822d524b90287a0af601c560074830c00000000092b8c419c7026c4343000000000c0560ed35107ad413800000000090a4d403670608c06552aa0000000000cae2c0a014242907f80000000008b1fe2c980000403fdc00fa03e000000000182d0000000000000000000f0516020652aa800008029b80fef23d0982e00000000000000417eb953c00003315d004cca6494144706c9c0f400002023e135120adf000000000000014041000000000e241a81c4000004123508380911f0407890c00944000090492c0d620b2f412bf0810c21d000034d8f0000240125036d0ac900000000000001c00e00000000000000000000000000090760000000000000000001c0d40097d81b7d0820011700003c17f300b5c087807e6c0af923ee0028e05a30133e2b71801190a7582d1a0a140000000000000207180000609b000000000000000000000000000000004023dc3126077c0000000000000103030acc800b08263008e2419e000030237005c4c2b96075f816700000805c801840000000008338106358a9f80c720af8502860d53000000000905bc000080bcc82a422b0c0000802fe002102c9442e24088ec27c00003c2dda05d98aa1b0caac0bd606f0000022cf9822e00000000020cbf8121d0c61006000000000010937ed3400000000000002c0b4803180000000000ace000000000d0bdc0000000020b0e000000000000000000000000000000000000c2360000020010cacb0000340270000000 else 0x9092c0000323a00000f03ba006fa2b87016ce2cf7c2c2000015c3d200bf40f7b01d502f230b78c106b057581750000000004012f42fb22a800000f039c00000000342b400000000000)))
def m3935d12 (i : Nat) : Nat := (if i<1 then 0x715f4a7b66811a02923506c865bf54c00afa528c0f38d670d007a34d90db7ca9a3a000f7984a5a90b40ced81fb21b6fd52d00148d283641ea9a383a0f5775045e3d0d6fd536291c260827010e2aa68680a00b14f42824155534758a06082518404aa68e80a1a3d0c89052021b16fd1c54c710d19120a40424adfaa6008e0a03224148be070b220905f0a4060b40cf142110502f8520305ac7019e2882817c290382d720413093e285a0611c20982d320411dbf54d0c4758b1c4347b7ea9a3a38868c8104f54d1c06530644706b4f2cddb1d2c01af02b39ab1aa53a8229b3a5028ffa282855a0027ab9d8270b9a3a62f979255394224b390da3a58cf22ab88ba1bb84aa0c181d9fef7d79eeb7aa9e417789d657419c7570d1ba36d89ad169a19d765e18f1618180b5e897395b6968f58c15c7561952752d14554f6138d4ce12f74a8921146c912b42e107740d8fa53d68efb3a48df73688d2f3278c532fa8b812cd8ac329e0a0526c093d237887f20d07cb1d606ef19f05ff15e04f1129845b10403a70dc03110ac825308981d105f013b03e80d702300410003ffd83a6510fff20e99443ffd73a6510fff60a99443ffd72a6510fff54a99443ffd32a6510fff66233443ffc988cd10fff65e33443ffd878cd10fff65a33443ffd868cd10fff5da33443ffd958cd10fff25633443ffc858cd10fff5d633443ffd658cd10fff64a33443ffc928cd10fff60a33443ffc828cd10fff5ca33443ffd628cd10fff54a33443ffc528cd10fff60633443ffd718cd10fff54633443ffd808cd10fff5c233443ffd608cd10fff54233443ffd208cd10fff66222443ffd9688910fff61a22443ffd9588910fff61622443ffc8588910fff59622443ffd9488910fff61222443ffd6488910fff55222443ffd9388910fff60e22443ffc8388910fff58e22443ffd5388910fff14e22443ffd4388910fff60622443ffd5188910fff50622443ffd3188910fff60222443ffd6088910fff54222443ffd3088910dff65e994437fd93a6510dff64a99443ff920a6510dff5d2994437fca3a6510dff60e994437fc83a6510dff5ce994437fd63a6510dff50e994437fca2a6510dff60a994437fc82a6510dff5ca994437fd62a6510dff54a994437fc52a6510dff50a994437fd32a6510dff0ca994437fd80a6510dff5c2994437fd50a6510dff4c2994437fd20a6510dff662334437fd978cd10dff65a334437fd958cd10ffd54633443ff9608cd10ffe482334437fd9888910dff65a224437fd9588910dff652224437fd9388910ffd54622443ff54188910ffe58222442ffd9344110bff60d10442ffd9244110bff60910442ffd5244110bff4c9104427fda7a65109ff692994427fda3a65109ff68a994427fca98cd109ff2a6224427fd93441109ff64910442ff92044110 else (if i<2 then 0x416ed9c8032a04dbe8125b47274e4048781064aa729219046a4dfc0065059c8ce2a075527702a06540fa1a07b7f5f811d572338a80d0407554e521e353e2be89d02caf271503204b7f5f2a50477dc5363005641672338a81d6f8de119ca0af6c06353501a0a012a9ca6861d9a919100057c5411764e2a070096febeef896293aae42089c38b5032dfd7e864a5df055007542d4e2a05d5394d0d830ced4b0c020c8afbe9e2a74113adfd7c4a77c04755c8ce1c5089554d0cfa78adb51ca09edfd7e86c190277d86ed9320b5d54e8226dbfafd5394bbed484f472040b3919c018113aa9a39b66a58e77c04e62c80303d5d53473e9642740f9aa9ca68e1e70e0f7980e9f417956fd1cefb1dcc590168181ea604a3b0e8018e0300a3a96ace31ab219470cc72d0c0573016be86c268ec38c25080c6383d4e7986a43a7d141179d6fd52d05908e07a6072a9ca467031a948c6907df46814146ac87552fa380d0590a0981cb7f5f0c80c77fb66801f4c9235051ab21d6fd52efb52cc009643400607aa810dfaa729801a90500c028e239738c6ac8755394c014301502340fa1a09aa7290f80c6a43f0f4140e9f468141179b025bfafc00efb1c54828060142d6718d590eb7ce5a180aed82d680d845bfafd5394f6c0fa340e341642aa9a39a905404e60761780c0f556fd1cef82bcc590168181ea6dfaa5a046ac84703d3dbf5491de2f30020180a87a9012a9a38676a58e7d2c84680c5553473e82f2821e9adfa39df63bb60b6c84680c48096fd52efb520a76c115908d018bb7e8e77d8e755c5159c810536fd53433be2b0480678a16b1c26082cb7ea9a39c81580c104f6fd534778a800ac06082897dd5721a074c4130c418825e28ac2631c20a0758a421818046a586c0b00189f4f15a0905d14c0c026058078b023e8d0265f085dfc004913b38755c86804771641686f14c0c1f352c33e8c778abb882b97e2981bc56804130c21782415b902098491d62983804185a963b02c680c7d1c8905d14c1c02730e43e8061e5f83804ce31a7544c905c84c5307078d4b1cfa78abbabc20aa5f1260e011df7158e75738c680c1602d722417cbf07009db73120baa06225f8a419079df6a5a007d23720415cbe24c5210808efb53800259c018d039120ba5f8a404ed9c86800c3c530740cc705be2818ef8ac20aa5f839df639d5135c5159c810552fc1d03018ea85a209e5f8a60677c2d63bc503122158415cbf14c1ce40ac060827aa6864d929419dff1700ce07ca8176fabeeae00e4670acd408aa6860e929419f44e3c55dd3aa8176fd0c16abe83600eae715026dfa19290b500c03b6756a04d534378abba749c5407b7ea941852ed902031c80fea055534726c94a1c1ee35813e80fd90baa68e0e929439f4e61755045e55bf4705aafa1c1eb538d6700fd90bb7ea9 else 0x154d0c23c5b066058078a71482aaa68611fc581302c01f409136fbbeeae058039116b1c23c82aaa68e11d8e77e2dc0b00f140c9056e4605804742389a6b7e8e77c4763830c0b007142d030d8905b6fd52ef88f16e0580125e281920ac04aa46fa19b66a5867d3c54eaa05f8a96a188251cfa0487012df77fb6755c84eaa044083da08323bf803aae4670e2d40baa6867d3c5a3941355394d0d8378a9c074fa54097d1d5721380e9dda80f6fd0cefb0ddb3aa16d408b7c6f4010ca393a75424450c7284616be8ea9d07b7c7cd7e0472338756a040754360c61284c3272fa274eaa715032dfaa5df6a))
def m3935l12 : Packing := (117,3,7,10,4,14,0,m3935d12)
def hashm3935l13 (i : Nat) : Nat := 0x1843000000004086000142e310000000000000003800ce0000426c92a0000a48c40680000000000209780000001c0fb00f2839000141240004920000000000004846000000000000000000000000000000000000000000000e054000000000000000000380600000000000180d00000000000241e8000000000000000000000000000000000000044d40928026c20e000000000000000000000069280000c17c000000000000001c18800000000000000000000000001081000000000000000092900018050838c1940000000000000000000402988580000001c05c00000000000000000000000000000101a8000000104240000000000000020250000a06800000000000000181b84348000000000000000000000000000077803000000034040000000000000000000000000000004055d0ba00000000000000000000000000405e00000000000000121c000000000000000000000001067009f095e91f00000000000082e10da000000038500001e09740ff8180001c4900000000000000000000000000000008398000b23cc1a08103848725c64b000000003202000181b486b000081580000000000000000000000000000000000000000000000000000000041630223851805000000001933501f418000000000000602c009000000000000000000000000000c320000c09e000183550528078000000000007372a0040000000a076e1000000000000000008b95800000000000000000d01200000000000000181780000000000000000000000000000000000000000000000006841000121300000000000000000000000000f40640337062e0b400000000000000120ac000000000000000000000040640000000000000000000000313400000003c8280000000000000078630001615043a00000001e04c00000000000000388700003049006e89959700000c13902590610000e008000001100000000000084700000000000000000000002c228000000041b000000000000000000000000000000000000000053608441d0000000000000000000000000038160000b021408c000401d700c000380a800000000000000000000000000000000000000002802b05bb0b320c109b2906e0e400000000000000000000000000c99a000000e0000000041bd8b8f8040000000242bc92d000000000002922000180dc0298000000105bb80b3822405a000000000000000000000000000000000149080000000e197c21083f000400000001000000050101000000050007000002030100030307000000050903000000000001
def m3935d13 (i : Nat) : Nat := 0x1bea94721a0500168338a41517c520e034e235c520a008dfafaa65286834038b38502c08dfafaa6528e87002711a063218df54a390c380d314828b9c997c4d007ffa6510bff4ca21ffe33443ffc44883ff44110
def m3935l13 : Packing := (5,2,7,7,4,9,0,m3935d13)
def m3935levels : Nat → Packing
  | 9 => m3935l9
  | 10 => m3935l10
  | 11 => m3935l11
  | 12 => m3935l12
  | 13 => m3935l13
  | _ => emptyPacking
def m3935index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun _ => none
  | 10 => lookupWord 12 103 7 14 6 4 (hashm3935l10)
  | 11 => lookupWord 188 998 8 18 10 4 (hashm3935l11)
  | 12 => lookupWord 279 2186 8 18 10 4 (hashm3935l12)
  | 13 => lookupWord 39 479 8 15 7 4 (hashm3935l13)
  | _ => fun _ => none
def m3935 : Forest := ⟨511,13,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,m3935levels,m3935index⟩
set_option maxHeartbeats 0 in
theorem geom3935 : graphValid m3935 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_9_0 : blockMono m3935 9 0 36 = true := by
  apply cellsBlockMono (ar:=10) (rows:=0) (d:=2)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blm3935_9 : blockMono m3935 9 0 36 = true := s3935_9_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_0 : blockMono m3935 10 0 1 = true := by
  apply cellsBlockMono (ar:=9) (rows:=0) (d:=0)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_1 : blockMono m3935 10 1 72 = true := by
  apply cellsBlockMono (ar:=10) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_73 : blockMono m3935 10 73 42 = true := by
  apply cellsBlockMono (ar:=10) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_115 : blockMono m3935 10 115 72 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_187 : blockMono m3935 10 187 72 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_259 : blockMono m3935 10 259 72 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_331 : blockMono m3935 10 331 72 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_403 : blockMono m3935 10 403 72 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_475 : blockMono m3935 10 475 72 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_10_547 : blockMono m3935 10 547 66 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blm3935_10 : blockMono m3935 10 0 613 = true := (@blockMono_merge m3935 10 0 547 66 (@blockMono_merge m3935 10 0 475 72 (@blockMono_merge m3935 10 0 403 72 (@blockMono_merge m3935 10 0 331 72 (@blockMono_merge m3935 10 0 259 72 (@blockMono_merge m3935 10 0 187 72 (@blockMono_merge m3935 10 0 115 72 (@blockMono_merge m3935 10 0 73 42 (@blockMono_merge m3935 10 0 1 72 s3935_10_0 s3935_10_1) s3935_10_73) s3935_10_115) s3935_10_187) s3935_10_259) s3935_10_331) s3935_10_403) s3935_10_475) s3935_10_547)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_0 : blockMono m3935 11 0 36 = true := by
  apply cellsBlockMono (ar:=10) (rows:=0) (d:=2)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_36 : blockMono m3935 11 36 72 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_108 : blockMono m3935 11 108 72 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_180 : blockMono m3935 11 180 72 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_252 : blockMono m3935 11 252 56 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_308 : blockMono m3935 11 308 72 = true := by
  apply cellsBlockMono (ar:=12) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_380 : blockMono m3935 11 380 72 = true := by
  apply cellsBlockMono (ar:=12) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_452 : blockMono m3935 11 452 72 = true := by
  apply cellsBlockMono (ar:=12) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_524 : blockMono m3935 11 524 72 = true := by
  apply cellsBlockMono (ar:=12) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_596 : blockMono m3935 11 596 72 = true := by
  apply cellsBlockMono (ar:=12) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_668 : blockMono m3935 11 668 72 = true := by
  apply cellsBlockMono (ar:=12) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_740 : blockMono m3935 11 740 72 = true := by
  apply cellsBlockMono (ar:=12) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_11_812 : blockMono m3935 11 812 28 = true := by
  apply cellsBlockMono (ar:=12) (rows:=0) (d:=2)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blm3935_11 : blockMono m3935 11 0 840 = true := (@blockMono_merge m3935 11 0 812 28 (@blockMono_merge m3935 11 0 740 72 (@blockMono_merge m3935 11 0 668 72 (@blockMono_merge m3935 11 0 596 72 (@blockMono_merge m3935 11 0 524 72 (@blockMono_merge m3935 11 0 452 72 (@blockMono_merge m3935 11 0 380 72 (@blockMono_merge m3935 11 0 308 72 (@blockMono_merge m3935 11 0 252 56 (@blockMono_merge m3935 11 0 180 72 (@blockMono_merge m3935 11 0 108 72 (@blockMono_merge m3935 11 0 36 72 s3935_11_0 s3935_11_36) s3935_11_108) s3935_11_180) s3935_11_252) s3935_11_308) s3935_11_380) s3935_11_452) s3935_11_524) s3935_11_596) s3935_11_668) s3935_11_740) s3935_11_812)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_12_0 : blockMono m3935 12 0 9 = true := by
  apply cellsBlockMono (ar:=10) (rows:=0) (d:=0)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_12_9 : blockMono m3935 12 9 47 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_12_56 : blockMono m3935 12 56 61 = true := by
  apply cellsBlockMono (ar:=12) (rows:=0) (d:=3)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blm3935_12 : blockMono m3935 12 0 117 = true := (@blockMono_merge m3935 12 0 56 61 (@blockMono_merge m3935 12 0 9 47 s3935_12_0 s3935_12_9) s3935_12_56)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_13_0 : blockMono m3935 13 0 1 = true := by
  apply cellsBlockMono (ar:=10) (rows:=0) (d:=0)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_13_1 : blockMono m3935 13 1 2 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=0)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_13_3 : blockMono m3935 13 3 1 = true := by
  apply cellsBlockMono (ar:=10) (rows:=0) (d:=0)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s3935_13_4 : blockMono m3935 13 4 1 = true := by
  apply cellsBlockMono (ar:=11) (rows:=0) (d:=0)
  simp only [cellsMono,boxesMono,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blm3935_13 : blockMono m3935 13 0 5 = true := (@blockMono_merge m3935 13 0 4 1 (@blockMono_merge m3935 13 0 3 1 (@blockMono_merge m3935 13 0 1 2 s3935_13_0 s3935_13_1) s3935_13_3) s3935_13_4)
theorem tables3935 : checkedTablesMono m3935 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : blockMono m3935 0 0 0 = true)
  · exact (rfl : blockMono m3935 1 0 0 = true)
  · exact (rfl : blockMono m3935 2 0 0 = true)
  · exact (rfl : blockMono m3935 3 0 0 = true)
  · exact (rfl : blockMono m3935 4 0 0 = true)
  · exact (rfl : blockMono m3935 5 0 0 = true)
  · exact (rfl : blockMono m3935 6 0 0 = true)
  · exact (rfl : blockMono m3935 7 0 0 = true)
  · exact (rfl : blockMono m3935 8 0 0 = true)
  · exact blm3935_9
  · exact blm3935_10
  · exact blm3935_11
  · exact blm3935_12
  · exact blm3935_13

def witnessBin (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

theorem gate_rep_mono (w : List Sig) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witnessBin w (gv w g) := by
  obtain ⟨o, l⟩ := g
  dsimp only at hop hl
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have bin_only : ∀ (d : Bool) {a b}, represented w a → represented w b →
      represented w (bin d a b) ∨ witnessBin w (bin d a b) := by
    intro d a b ha hb
    have h1 := bin_rep d ha hb
    rcases operand_cases ha with rfl | rfl | ⟨ham, hap⟩
    · rw [bin_comm]; cases d <;> simp_all [bin_laws]
    · rw [bin_comm]; cases d <;> simp_all [bin_laws]
    rcases operand_cases hb with rfl | rfl | ⟨hbm, hbp⟩
    · cases d <;> simp_all [bin_laws]
    · cases d <;> simp_all [bin_laws]
    by_cases he : a = b
    · subst b; cases d <;> simp_all [bin_laws]
    · exact Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases hop with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using
          Or.inl (b := witnessBin w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using
          Or.inl (b := witnessBin w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases hop with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using
            bin_only false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using
            bin_only true (get_rep w i) (get_rep w j)

theorem pull_gate_mono {w : List Sig} {z : Sig} {k S} (h : Live target k 0 S)
    (hz : represented w z ∨ witnessBin w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + 1 ∧ Live target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k 0 (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k + 1, insert a (insert b U), Nat.le_refl _, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem extract_mono (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live target k 0 S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {target}, by simp, Live.stop hp, by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) hout
    have hlg := legal g (by simp)
    obtain ⟨l, T, hl, hu, hT⟩ := pull_gate_mono ht (gate_rep_mono w g hlg.1 hlg.2) hs
    exact ⟨l, T, by simp; omega, hu, hT⟩

theorem raw_required_mono {T k S} (h : Live T k 0 S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (ht : bit r T = true) (hf : bit s T = false)
    (isolated : ∀ v ∈ roots, v ≠ a → !(bit r v && !bit s v) = true) : a ∈ S := by
  obtain ⟨v, hv, hr, hs⟩ := mono_row_difference h rfl ht hf
  by_cases veq : v = a
  · simpa [veq] using hv
  · have hi := isolated v (sub v hv) veq
    simp [hr, hs] at hi

def base10 : List Sig := inputs ++ [or01]
def nb3935 (i : Fin 9) : Nat := [1,0,1,2,3,0,1,2,3].getD i.val 0
def absRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< nb3935 i)
def presRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< nb3935 i))

theorem mono_witness_all :
    (∀ i : Fin 9, bit (presRow i) graph = true ∧ bit (absRow i) graph = false) ∧
    (∀ i : Fin 9, ∀ j : Fin 10,
      ((inputs ++ [or01, neg (base10.getD j.val zero)]).all fun w =>
        w == inputs.getD i.val zero || !(bit (presRow i) w && !bit (absRow i) w)) = true) ∧
    (∀ i : Fin 9,
      ((inputs ++ [or01, one]).all fun w =>
        w == inputs.getD i.val zero || !(bit (presRow i) w && !bit (absRow i) w)) = true) := by
  decide +kernel

theorem chart511_eq : chartGoal 511 = graph := by decide +kernel

def cutByColB (ci : ColumnInfo) (cs : List Choice) (ws : List Sig) : Bool :=
  match makePool (subcube ci.1 ci.2.1) (vars 511) cs with
  | none => false
  | some pool => poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 13 cs.length pool ws

theorem cutByCol (ci : ColumnInfo) (cs : List Choice) (ws : List Sig)
    (hcol : colCheck 511 ci (boundsBefore known383) = true)
    (hpool : cutByColB ci cs ws = true)
    (hnd : ws.Nodup) : ImpossibleMono graph 13 ws.toFinset := by
  have hlow := before_sound known383 valid383
  have hslice : Slice (vars 511) graph (subcube ci.1 ci.2.1) ci.2.2.2.2 := by
    have hs := col_sound ci (boundsBefore known383) hlow hcol
    rwa [chart511_eq] at hs
  unfold cutByColB at hpool
  cases hmp : makePool (subcube ci.1 ci.2.1) (vars 511) cs with
  | none => simp [hmp] at hpool
  | some pool =>
    simp only [hmp] at hpool
    exact imp_mono (poolCut_sound hslice cs hmp hnd hpool)

theorem root_imp (i : Nat) (ws : List Sig) (h : indexedRoot m3935 13 i ws = true) :
    ImpossibleMono graph 13 ws.toFinset := by
  have hi := root_index_mono (g := m3935) (before_sound known383 valid383) geom3935 tables3935 (le_refl 13) h
  have ht : targetOf m3935 = graph := chart511_eq
  exact ht ▸ hi

theorem root_imp_rot (i : Nat) (ws rs : List Sig) (p : List Nat)
    (h : indexedRoot m3935 13 i rs = true)
    (ha : autoOK graph (p.map swapRows) = true)
    (hs : sameWords (rs.map (movedWord (p.map swapRows).reverse)) ws = true) :
    ImpossibleMono graph 13 ws.toFinset := by
  rw [← sameWords_sound hs]
  exact rotate_excluded_mono (root_imp i rs h) _ ha

theorem imp_inputs : ImpossibleMono graph 13 inputs.toFinset :=
  cutByCol (16,0,495,0,13) [] inputs (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem imp_or01 : ImpossibleMono graph 13 (inputs ++ [or01]).toFinset :=
  root_imp 0 (inputs ++ [or01]) (by decide +kernel)

theorem imp_v1 (j : Fin 10) : ImpossibleMono graph 13 (inputs ++ [neg (base10.getD j.val zero)]).toFinset := by
  fin_cases j
  · exact cutByCol (1,0,510,0,12) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (2,0,509,0,12) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (4,0,507,0,12) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (8,0,503,0,12) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (16,0,495,0,13) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (32,0,479,0,12) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (64,0,447,0,13) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (128,0,383,0,13) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (256,0,255,0,12) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact root_imp 3 _ (by decide +kernel)

theorem imp_or01_v1 (j : Fin 10) : ImpossibleMono graph 13 (inputs ++ [or01, neg (base10.getD j.val zero)]).toFinset := by
  fin_cases j
  · exact cutByCol (1,0,510,0,12) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (2,0,509,0,12) [] _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact root_imp 1 _ (by decide +kernel)
  · exact root_imp 2 _ (by decide +kernel)
  · exact cutByCol (16,0,495,0,13) [(1, inputs.getD 0 zero, inputs.getD 1 zero)] _
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact root_imp_rot 1 _ (inputs ++ [or01, neg (base10.getD 2 zero)]) [100,131,82,16]
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (64,0,447,0,13) [(1, inputs.getD 0 zero, inputs.getD 1 zero)] _
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact cutByCol (128,0,383,0,13) [(1, inputs.getD 0 zero, inputs.getD 1 zero)] _
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact root_imp_rot 2 _ (inputs ++ [or01, neg (base10.getD 3 zero)]) [100,131,82,16]
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact root_imp 4 _ (by decide +kernel)

theorem all_roots_one {k S} (h : Live graph k 0 S) (sub : ∀ v ∈ S, v ∈ inputs ++ [or01, one]) :
    S = inputs.toFinset ∨ S = (inputs ++ [or01]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have hw := mono_witness_all.2.2 i
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hw
    exact raw_required_mono h _ _ sub (presRow i) (absRow i)
      (mono_witness_all.1 i).1 (mono_witness_all.1 i).2 (fun v hv hne => (hw v hv).resolve_left hne)
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [← input_list, List.mem_ofFn] at hm
    obtain ⟨i, rfl⟩ := hm
    exact all i
  have noOne : one ∉ S := fun hm => (live_proper h one hm).2 rfl
  by_cases hor : or01 ∈ S
  · right
    ext w
    constructor
    · intro hw
      have hx := sub w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hin | rfl | rfl
      · exact List.mem_toFinset.mpr (List.mem_append_left _ hin)
      · exact List.mem_toFinset.mpr (by simp)
      · exact False.elim (noOne hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append, List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hor)
  · left
    ext w
    constructor
    · intro hw
      have hx := sub w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hin | rfl | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hor hw)
      · exact False.elim (noOne hw)
    · intro hw
      exact needed hw

theorem all_roots_neg (j : Fin 10) {k S} (h : Live graph k 0 S)
    (sub : ∀ v ∈ S, v ∈ inputs ++ [or01, neg (base10.getD j.val zero)]) :
    S = inputs.toFinset ∨ S = (inputs ++ [or01]).toFinset ∨
    S = (inputs ++ [neg (base10.getD j.val zero)]).toFinset ∨
    S = (inputs ++ [or01, neg (base10.getD j.val zero)]).toFinset := by
  let v1 := neg (base10.getD j.val zero)
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have hw := mono_witness_all.2.1 i j
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hw
    exact raw_required_mono h _ _ sub (presRow i) (absRow i)
      (mono_witness_all.1 i).1 (mono_witness_all.1 i).2 (fun v hv hne => (hw v hv).resolve_left hne)
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [← input_list, List.mem_ofFn] at hm
    obtain ⟨i, rfl⟩ := hm
    exact all i
  by_cases hor : or01 ∈ S <;> by_cases hv1 : v1 ∈ S
  · right; right; right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hin | rfl | rfl
      · exact needed (List.mem_toFinset.mpr hin)
      · exact hor
      · exact hv1
  · right; left
    ext w
    constructor
    · intro hw
      have hx := sub w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hin | rfl | rfl
      · exact List.mem_toFinset.mpr (List.mem_append_left _ hin)
      · exact List.mem_toFinset.mpr (by simp)
      · exact False.elim (hv1 hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append, List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hor)
  · right; right; left
    ext w
    constructor
    · intro hw
      have hx := sub w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hin | rfl | rfl
      · exact List.mem_toFinset.mpr (List.mem_append_left _ hin)
      · exact False.elim (hor hw)
      · exact List.mem_toFinset.mpr (by simp)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append, List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hv1)
  · left
    ext w
    constructor
    · intro hw
      have hx := sub w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hin | rfl | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hor hw)
      · exact False.elim (hv1 hw)
    · intro hw
      exact needed hw

theorem mono_close (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge)
    (hnot1 : ∃ g : Gate, C.gates[1]? = Option.some g ∧ g.op = GateOp.not)
    (hnc1 : C.gates.countP (fun g => g.op.eval [false]) ≤ 1)
    (small : C.size ≤ 15) : False := by
  have headEq : (execute C.gates inputs).getD 9 zero = or01 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (or01_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨g1, hg1, hg1op⟩ := hnot1
  cases hgs : C.gates with
  | nil => rw [hgs] at hg1; simp at hg1
  | cons g0 tl =>
    cases htl : tl with
    | nil => rw [hgs, htl] at hg1; simp at hg1
    | cons g1' rest =>
      rw [hgs, htl] at hg1
      have hg1eq : g1' = g1 := Option.some.inj hg1
      subst hg1eq
      have eq0 : gv inputs g0 = or01 := by
        rw [hgs, htl] at headEq
        change (execute (g1' :: rest) (inputs ++ [gv inputs g0])).getD 9 zero = or01 at headEq
        obtain ⟨l, hl⟩ := exec_extends (g1' :: rest) (inputs ++ [gv inputs g0])
        rw [hl] at headEq
        have hlen9 : inputs.length = 9 := rfl
        have hassoc : (inputs ++ [gv inputs g0]) ++ l = inputs ++ (gv inputs g0 :: l) := by simp
        rw [hassoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)] at headEq
        simpa [hlen9] using headEq
      rw [hgs, htl] at targetIn
      change graph ∈ execute rest ((inputs ++ [gv inputs g0]) ++ [gv (inputs ++ [gv inputs g0]) g1']) at targetIn
      rw [eq0] at targetIn
      have hlen : rest.length ≤ 13 := by
        have : C.size = rest.length + 2 := by simp [Circuit.size, hgs, htl]
        omega
      have hnc_rest : rest.countP (fun g => g.op.eval [false]) = 0 := by
        rw [hgs, htl] at hnc1
        have hp : GateOp.not.eval [false] = true := rfl
        simp only [List.countP_cons, hg1op, hp, ite_true] at hnc1
        omega
      have rest_mono : ∀ g ∈ rest, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        have hlg := legal g (by rw [hgs, htl]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
        refine ⟨?_, hlg.2⟩
        rcases hlg.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso
          have hpos : 0 < rest.countP (fun q => q.op.eval [false]) :=
            List.countP_pos_iff.mpr ⟨g, hg, by rw [h]; rfl⟩
          omega
      have hbase : (inputs ++ [or01]) ++ [gv (inputs ++ [or01]) g1'] =
          inputs ++ [or01, gv (inputs ++ [or01]) g1'] := by simp
      rw [hbase] at targetIn
      obtain ⟨k, S, hk, hlive, hsub⟩ := extract_mono rest _ rest_mono graph_proper targetIn
      have hk13 : k ≤ 13 := by omega
      have hneg0 : neg zero = one := by decide +kernel
      have hb10len : base10.length = 10 := rfl
      have hv1 : gv (inputs ++ [or01]) g1' = one ∨ ∃ j : Fin 10, gv (inputs ++ [or01]) g1' = neg (base10.getD j.val zero) := by
        change gv base10 g1' = one ∨ _
        unfold gv
        rw [hg1op]
        cases hin : g1'.inputs with
        | nil => left; exact hneg0
        | cons idx _ =>
          simp only [List.map_cons, List.headD_cons]
          by_cases hlt : idx < 10
          · exact Or.inr ⟨⟨idx, hlt⟩, rfl⟩
          · left
            have hdef : base10.getD idx zero = zero := List.getD_eq_default _ _ (by omega)
            rw [hdef]; exact hneg0
      rcases hv1 with hv1 | ⟨j, hv1⟩
      · rw [hv1] at hsub
        rcases all_roots_one hlive hsub with rfl | rfl
        · exact imp_inputs k hk13 hlive
        · exact imp_or01 k hk13 hlive
      · rw [hv1] at hsub
        rcases all_roots_neg j hlive hsub with rfl | rfl | rfl | rfl
        · exact imp_inputs k hk13 hlive
        · exact imp_or01 k hk13 hlive
        · exact imp_v1 j k hk13 hlive
        · exact imp_or01_v1 j k hk13 hlive
end P2
end PEqualNP.Outside.L_meta_3935
theorem PEqualNP.Outside.L_meta_3935 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin (9 : ℕ)) (x6 : Finset ℕ), (∀ x7 ∈ x6, x7 < x1.size ∧ ((∃ (x9 : Bool), ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = x9) ∨ ∃ x9 < (9 : ℕ) + x7, ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = (x1.wires (List.ofFn x10)).getD x9 Bool.false)) → (x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] → x6.card ≤ (3 : ℕ)) ∧ (x5 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x6.card ≤ (2 : ℕ))) → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (16 : ℕ) ≤ x1.size := by
  intro C hC hfirst hlisted _ hnot1
  have hfun : PEqualNP.MetaComplexity.circuitFun 9 C = PEqualNP.Outside.L_meta_3935.P1.fG := by
    rw [hlisted]
    funext x
    simp [PEqualNP.Outside.L_meta_3935.P1.fG, List.any, Bool.or_assoc]
  by_contra hlt
  have hsize : C.size ≤ 15 := by omega
  by_cases hnc : 2 ≤ PEqualNP.Outside.L_meta_3935.P1.nc C.gates
  · exact PEqualNP.Outside.L_meta_3935.P1.no15 1 rfl C hC hsize hfirst hnc hfun
  · have hnc1 : C.gates.countP (fun g => g.op.eval [false]) ≤ 1 := by
      change ¬ 2 ≤ C.gates.countP (fun g => g.op.eval [false]) at hnc
      omega
    have hedge : PEqualNP.MetaComplexity.circuitFun 9 C = PEqualNP.Outside.L_meta_3935.P2.edge := by
      rw [hlisted]
      funext x
      simp [PEqualNP.Outside.L_meta_3935.P2.edge, List.any, Bool.or_assoc]
    exact PEqualNP.Outside.L_meta_3935.P2.mono_close C hC hfirst hedge hnot1 hnc1 hsize
