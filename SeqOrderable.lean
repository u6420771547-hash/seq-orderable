/-
  Formal Proof of Theorem A (Resolving Conjecture 10 of Gorzkowska & Kwaśny, 2026):
  Every proper d-edge-colouring of a 2-connected d-regular simple graph (d ≥ 3)
  is sequentially orderable.

  Standalone Lean 4.36.0 file (no external dependencies, zero sorry).
-/

namespace SeqOrderable

/-! ## Section 1: List, Pigeonhole, and Permutation Helpers -/

theorem nodup_length_le_of_subset {α : Type} [DecidableEq α]
    (l₁ l₂ : List α) (hnd : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) :
    l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l₂ := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ c ∈ l, c ∈ l₂.erase a := by
      intro c hc
      have hne : c ≠ a := fun hca => hnd.1 (hca ▸ hc)
      exact (List.mem_erase_of_ne hne).mpr (hsub c (List.mem_cons_of_mem _ hc))
    have hle' := ih (l₂.erase a) hnd.2 hsub'
    have hpos : 0 < l₂.length := List.length_pos_of_mem ha
    have herase : (l₂.erase a).length = l₂.length - 1 := List.length_erase_of_mem ha
    simp only [List.length_cons]
    omega

theorem pigeonhole_list {α : Type} [DecidableEq α]
    (cands forb : List α) (hnd : cands.Nodup) (hlt : forb.length < cands.length) :
    ∃ c ∈ cands, c ∉ forb := by
  apply Classical.byContradiction
  intro h
  have hsub : ∀ c ∈ cands, c ∈ forb := by
    intro c hc
    apply Classical.byContradiction
    intro hnf
    exact h ⟨c, hc, hnf⟩
  have hle := nodup_length_le_of_subset cands forb hnd hsub
  omega

theorem nodup_map_inj {α β : Type} (f : α → β) (l : List α)
    (hnd : l.Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hnd.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    rintro ⟨b, hb, hfb⟩
    have hba : b = a := hinj b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) hfb
    exact hnd.1 (hba ▸ hb)

theorem nodup_append_iff {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).Nodup ↔ l₁.Nodup ∧ l₂.Nodup ∧ ∀ x ∈ l₁, x ∉ l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons, not_or, ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, hnd1, hnd2, hdisj⟩
      refine ⟨⟨h1, hnd1⟩, hnd2, fun x hx => ?_⟩
      cases hx with
      | inl hxa => subst hxa; exact h2
      | inr hxl => exact hdisj x hxl
    · rintro ⟨⟨h1, hnd1⟩, hnd2, hdisj⟩
      refine ⟨⟨h1, hdisj a (Or.inl rfl)⟩, hnd1, hnd2, fun x hx => hdisj x (Or.inr hx)⟩

theorem nodup_flatMap_of {α β : Type} (f : α → List β) (l : List α)
    (hnd : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ y ∈ f a, y ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.flatMap_cons]
    rw [nodup_append_iff]
    refine ⟨hf a (List.mem_cons_self ..), ?_, ?_⟩
    · exact ih hnd.2
        (fun b hb => hf b (List.mem_cons_of_mem _ hb))
        (fun b hb c hc hne => hdisj b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) hne)
    · intro y hya hyrest
      rw [List.mem_flatMap] at hyrest
      obtain ⟨b, hb, hyb⟩ := hyrest
      have hne : a ≠ b := fun hab => hnd.1 (hab ▸ hb)
      exact hdisj a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) hne y hya hyb

theorem sum_map_const {α : Type} (l : List α) (c : Nat) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.succ_mul, Nat.add_comm]

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem lt_fact_pred : ∀ d : Nat, 4 ≤ d → d < fact (d - 1)
  | 0, hd => by omega
  | 1, hd => by omega
  | 2, hd => by omega
  | 3, hd => by omega
  | 4, _ => by decide
  | k + 5, _ => by
    have ih : k + 4 < fact (k + 3) := lt_fact_pred (k + 4) (by omega)
    show k + 5 < (k + 4) * fact (k + 3)
    have h1 : (k + 4) * (k + 4) < (k + 4) * fact (k + 3) :=
      Nat.mul_lt_mul_of_pos_left ih (by omega)
    have h2 : k + 5 ≤ (k + 4) * (k + 4) := by
      have : 2 * (k + 4) ≤ (k + 4) * (k + 4) := Nat.mul_le_mul_right (k + 4) (by omega)
      omega
    omega

/-- Insert `x` at index `i` of `l`. -/
def insertAt {α : Type} (x : α) : Nat → List α → List α
  | 0, l => x :: l
  | _ + 1, [] => [x]
  | i + 1, a :: l => a :: insertAt x i l

theorem mem_insertAt {α : Type} (x y : α) (i : Nat) (l : List α) :
    y ∈ insertAt x i l ↔ y = x ∨ y ∈ l := by
  induction i generalizing l with
  | zero => simp [insertAt]
  | succ i ih =>
    cases l with
    | nil => simp [insertAt]
    | cons a l =>
      simp only [insertAt, List.mem_cons, ih]
      exact ⟨fun h => by rcases h with h | h | h <;> simp [h],
             fun h => by rcases h with h | h | h <;> simp [h]⟩

theorem length_insertAt {α : Type} (x : α) (i : Nat) (l : List α) :
    (insertAt x i l).length = l.length + 1 := by
  induction i generalizing l with
  | zero => simp [insertAt]
  | succ i ih =>
    cases l with
    | nil => simp [insertAt]
    | cons a l => simp [insertAt, ih]

theorem nodup_insertAt {α : Type} (x : α) (i : Nat) (l : List α)
    (hnd : l.Nodup) (hx : x ∉ l) : (insertAt x i l).Nodup := by
  induction i generalizing l with
  | zero => simp [insertAt, List.nodup_cons, hx, hnd]
  | succ i ih =>
    cases l with
    | nil => simp [insertAt]
    | cons a l =>
      rw [List.nodup_cons] at hnd
      simp only [List.mem_cons, not_or] at hx
      simp only [insertAt, List.nodup_cons, mem_insertAt, not_or]
      exact ⟨⟨Ne.symm hx.1, hnd.1⟩, ih l hnd.2 hx.2⟩

theorem filter_insertAt_false {α : Type} (p : α → Bool) (x : α) (i : Nat) (l : List α)
    (hp : p x = false) : (insertAt x i l).filter p = l.filter p := by
  induction i generalizing l with
  | zero => simp [insertAt, hp]
  | succ i ih =>
    cases l with
    | nil => simp [insertAt, hp]
    | cons a l =>
      simp only [insertAt, List.filter_cons]
      cases hpa : p a <;> simp [ih]

/-- All `l.length + 1` ways to insert `x` into `l`. -/
def allInserts {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | a :: l => (x :: a :: l) :: (allInserts x l).map (a :: ·)

/-- All permutations of a list. -/
def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => (perms l).flatMap (allInserts a)

theorem length_allInserts {α : Type} (x : α) (l : List α) :
    (allInserts x l).length = l.length + 1 := by
  induction l with
  | nil => simp [allInserts]
  | cons a l ih => simp [allInserts, ih]

theorem mem_allInserts_iff {α : Type} (x : α) (l r : List α) :
    r ∈ allInserts x l ↔ ∃ i ≤ l.length, r = insertAt x i l := by
  induction l generalizing r with
  | nil =>
    simp only [allInserts, List.mem_singleton, List.length_nil]
    constructor
    · intro h; exact ⟨0, Nat.le_refl 0, h⟩
    · rintro ⟨i, hi, rfl⟩
      have : i = 0 := Nat.le_zero.mp hi
      subst this; rfl
  | cons a l ih =>
    simp only [allInserts, List.mem_cons, List.mem_map, List.length_cons]
    constructor
    · rintro (rfl | ⟨r', hr', rfl⟩)
      · exact ⟨0, Nat.zero_le _, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := (ih r').mp hr'
        exact ⟨i + 1, Nat.succ_le_succ hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => left; rfl
      | succ i =>
        right
        exact ⟨insertAt x i l, (ih _).mpr ⟨i, Nat.le_of_succ_le_succ hi, rfl⟩, rfl⟩

theorem nodup_allInserts {α : Type} (x : α) (l : List α) (hx : x ∉ l) :
    (allInserts x l).Nodup := by
  induction l with
  | nil => simp [allInserts]
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at hx
    simp only [allInserts, List.nodup_cons]
    constructor
    · intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨r, _, hreq⟩ := hmem
      simp only [List.cons.injEq] at hreq
      exact hx.1 hreq.1.symm
    · exact nodup_map_inj (a :: ·) (allInserts x l) (ih hx.2) (fun _ _ _ _ h => (List.cons.inj h).2)

theorem perm_insertAt {α : Type} (x : α) (i : Nat) (l : List α) :
    List.Perm (insertAt x i l) (x :: l) := by
  induction i generalizing l with
  | zero => exact List.Perm.refl _
  | succ i ih =>
    cases l with
    | nil => exact List.Perm.refl _
    | cons a l =>
      exact (List.Perm.cons a (ih l)).trans (List.Perm.swap x a l)

theorem perms_perm {α : Type} (l p : List α) (hp : p ∈ perms l) :
    List.Perm p l := by
  induction l generalizing p with
  | nil =>
    simp only [perms, List.mem_singleton] at hp
    subst hp; exact List.Perm.refl _
  | cons a l ih =>
    simp only [perms, List.mem_flatMap] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    obtain ⟨i, _, rfl⟩ := (mem_allInserts_iff a q p).mp hpq
    exact (perm_insertAt a i q).trans (List.Perm.cons a (ih q hq))

theorem length_perms {α : Type} (l : List α) : (perms l).length = fact l.length := by
  induction l with
  | nil => simp [perms, fact]
  | cons a l ih =>
    simp only [perms, List.length_flatMap, List.length_cons, fact]
    have hmap : (perms l).map (fun q => (allInserts a q).length) =
        (perms l).map (fun _ => l.length + 1) := by
      apply List.map_congr_left
      intro q hq
      rw [length_allInserts, (perms_perm l q hq).length_eq]
    rw [hmap, sum_map_const, ih, Nat.mul_comm]

theorem insertAt_eq_cancel {α : Type} (a : α) :
    ∀ (q₁ q₂ : List α) (i₁ i₂ : Nat),
      a ∉ q₁ → a ∉ q₂ → insertAt a i₁ q₁ = insertAt a i₂ q₂ → q₁ = q₂ := by
  intro q₁
  induction q₁ with
  | nil =>
    intro q₂ i₁ i₂ _ h2 h
    cases i₁ <;> cases q₂ <;> cases i₂ <;> simp [insertAt] at h ⊢
    all_goals (simp only [List.mem_cons, not_or] at h2; exact absurd h.1 h2.1)
  | cons b q₁ ihq =>
    intro q₂ i₁ i₂ h1 h2 h
    simp only [List.mem_cons, not_or] at h1
    cases i₁ with
    | zero =>
      cases i₂ with
      | zero => simp [insertAt] at h; exact h
      | succ i₂ =>
        cases q₂ with
        | nil => simp [insertAt] at h
        | cons c q₂ =>
          simp only [List.mem_cons, not_or] at h2
          simp [insertAt] at h
          exact absurd h.1 h2.1
    | succ i₁ =>
      cases i₂ with
      | zero =>
        simp [insertAt] at h
        exact absurd h.1.symm h1.1
      | succ i₂ =>
        cases q₂ with
        | nil =>
          simp [insertAt] at h
          exact absurd h.1.symm h1.1
        | cons c q₂ =>
          simp only [List.mem_cons, not_or] at h2
          simp [insertAt] at h
          rw [h.1, ihq q₂ i₁ i₂ h1.2 h2.2 h.2]

theorem nodup_perms {α : Type} (l : List α) (hnd : l.Nodup) : (perms l).Nodup := by
  induction l with
  | nil => simp [perms]
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [perms]
    apply nodup_flatMap_of (allInserts a) (perms l) (ih hnd.2)
    · intro q hq
      have ha : a ∉ q := fun haq => hnd.1 ((perms_perm l q hq).subset haq)
      exact nodup_allInserts a q ha
    · intro q₁ hq₁ q₂ hq₂ hne r hr₁ hr₂
      obtain ⟨i₁, _, hr1eq⟩ := (mem_allInserts_iff a q₁ r).mp hr₁
      obtain ⟨i₂, _, hr2eq⟩ := (mem_allInserts_iff a q₂ r).mp hr₂
      have heq : insertAt a i₁ q₁ = insertAt a i₂ q₂ := hr1eq.symm.trans hr2eq
      have ha₁ : a ∉ q₁ := fun haq => hnd.1 ((perms_perm l q₁ hq₁).subset haq)
      have ha₂ : a ∉ q₂ := fun haq => hnd.1 ((perms_perm l q₂ hq₂).subset haq)
      exact hne (insertAt_eq_cancel a q₁ q₂ i₁ i₂ ha₁ ha₂ heq)

/-! ## Section 2: Finite Simple Graphs, Edges, Colourings, and Connectivity -/

structure Graph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

structure Edge (n : Nat) where
  u : Fin n
  v : Fin n
  hlt : u.val < v.val
  deriving DecidableEq

def mkEdge {n : Nat} (a b : Fin n) (h : a ≠ b) : Edge n :=
  if hlt : a.val < b.val then
    ⟨a, b, hlt⟩
  else
    ⟨b, a, by
      have : a.val ≠ b.val := fun heq => h (Fin.ext heq)
      omega⟩

theorem mkEdge_symm {n : Nat} (a b : Fin n) (h : a ≠ b) :
    mkEdge a b h = mkEdge b a h.symm := by
  unfold mkEdge
  split <;> split
  · omega
  · rfl
  · rfl
  · have : a.val ≠ b.val := fun heq => h (Fin.ext heq)
    omega

def Edge.incident {n : Nat} (e : Edge n) (x : Fin n) : Bool :=
  (e.u == x) || (e.v == x)

def Edge.isEdge {n : Nat} (G : Graph n) (e : Edge n) : Bool :=
  G.adj e.u e.v

theorem mkEdge_incident {n : Nat} (a b x : Fin n) (h : a ≠ b) :
    (mkEdge a b h).incident x = true ↔ x = a ∨ x = b := by
  unfold mkEdge Edge.incident
  split
  · simp only [Bool.or_eq_true, beq_iff_eq]
    exact ⟨fun p => p.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm),
           fun p => p.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  · simp only [Bool.or_eq_true, beq_iff_eq]
    exact ⟨fun p => p.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm),
           fun p => p.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩

theorem mkEdge_isEdge {n : Nat} (G : Graph n) (a b : Fin n) (h : a ≠ b) :
    (mkEdge a b h).isEdge G = G.adj a b := by
  unfold mkEdge Edge.isEdge
  split
  · rfl
  · exact G.symm b a

theorem edge_ne_of_adj {n : Nat} (G : Graph n) {a b : Fin n} (h : G.adj a b = true) :
    a ≠ b := by
  intro hab
  subst hab
  rw [G.loopless] at h
  cases h

theorem edge_eq_mkEdge {n : Nat} (e : Edge n) (x y : Fin n)
    (hx : e.incident x = true) (hy : e.incident y = true) (hne : x ≠ y) :
    e = mkEdge x y hne := by
  rcases e with ⟨u, v, hlt⟩
  simp only [Edge.incident, Bool.or_eq_true, beq_iff_eq] at hx hy
  unfold mkEdge
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hne
  · simp [hlt]
  · have hnot : ¬ (v.val < u.val) := by omega
    simp [hnot]
  · exact absurd rfl hne

def Graph.nbrs {n : Nat} (G : Graph n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun u => G.adj v u)

def Graph.deg {n : Nat} (G : Graph n) (v : Fin n) : Nat :=
  (G.nbrs v).length

def Graph.IsRegular {n : Nat} (G : Graph n) (d : Nat) : Prop :=
  ∀ v : Fin n, G.deg v = d

theorem mem_nbrs {n : Nat} (G : Graph n) (v u : Fin n) :
    u ∈ G.nbrs v ↔ G.adj v u = true := by
  simp [Graph.nbrs]

theorem nodup_nbrs {n : Nat} (G : Graph n) (v : Fin n) : (G.nbrs v).Nodup :=
  (List.nodup_finRange n).filter _

def Graph.incEdges {n : Nat} (G : Graph n) (v : Fin n) : List (Edge n) :=
  (G.nbrs v).attach.map (fun ⟨u, hu⟩ => mkEdge v u (edge_ne_of_adj G ((mem_nbrs G v u).mp hu)))

theorem mem_incEdges {n : Nat} (G : Graph n) (v : Fin n) (e : Edge n) :
    e ∈ G.incEdges v ↔ e.isEdge G = true ∧ e.incident v = true := by
  unfold Graph.incEdges
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hadj := (mem_nbrs G v u).mp hu
    exact ⟨by rw [mkEdge_isEdge]; exact hadj, (mkEdge_incident v u v _).mpr (Or.inl rfl)⟩
  · rintro ⟨he, hinc⟩
    rcases e with ⟨a, b, hlt⟩
    simp only [Edge.incident, Bool.or_eq_true, beq_iff_eq] at hinc
    simp only [Edge.isEdge] at he
    rcases hinc with rfl | rfl
    · refine ⟨b, (mem_nbrs G a b).mpr he, ?_⟩
      exact (edge_eq_mkEdge ⟨a, b, hlt⟩ a b (by simp [Edge.incident]) (by simp [Edge.incident]) _).symm
    · have hba : G.adj b a = true := by rw [G.symm]; exact he
      refine ⟨a, (mem_nbrs G b a).mpr hba, ?_⟩
      exact (edge_eq_mkEdge ⟨a, b, hlt⟩ b a (by simp [Edge.incident]) (by simp [Edge.incident]) _).symm

/-- Proper edge colouring with colours in `C`. -/
def IsProperEdgeColoring {n : Nat} {C : Type} (G : Graph n) (w : Edge n → C) : Prop :=
  ∀ e₁ e₂ : Edge n, e₁.isEdge G = true → e₂.isEdge G = true →
    e₁ ≠ e₂ → (∃ x : Fin n, e₁.incident x = true ∧ e₂.incident x = true) →
    w e₁ ≠ w e₂

/-- Induced vertex sequence under a global edge ordering list `L`. -/
def vertexSeq {n : Nat} {C : Type} (w : Edge n → C) (L : List (Edge n)) (v : Fin n) : List C :=
  (L.filter (fun e => e.incident v)).map w

/-- A list `L` is a complete ordering of `E(G)`. -/
def IsEdgeOrder {n : Nat} (G : Graph n) (L : List (Edge n)) : Prop :=
  L.Nodup ∧ ∀ e : Edge n, e ∈ L ↔ e.isEdge G = true

/-- A proper edge colouring `w` is sequentially orderable if some edge order `L`
    induces a proper vertex colouring. -/
def SequentiallyOrderable {n : Nat} {C : Type} (G : Graph n) (w : Edge n → C) : Prop :=
  ∃ L : List (Edge n), IsEdgeOrder G L ∧
    ∀ u v : Fin n, G.adj u v = true → vertexSeq w L u ≠ vertexSeq w L v

/-- Reachability inside an induced subgraph `S : Fin n → Bool`. -/
inductive Reachable {n : Nat} (G : Graph n) (S : Fin n → Bool) : Fin n → Fin n → Prop where
  | refl {u} : S u = true → Reachable G S u u
  | step {u w v} : S u = true → G.adj u w = true → Reachable G S w v → Reachable G S u v

theorem Reachable.target_mem {n : Nat} {G : Graph n} {S : Fin n → Bool} {u v : Fin n}
    (h : Reachable G S u v) : S v = true := by
  induction h with
  | refl hu => exact hu
  | step _ _ _ ih => exact ih

theorem Reachable.source_mem {n : Nat} {G : Graph n} {S : Fin n → Bool} {u v : Fin n}
    (h : Reachable G S u v) : S u = true := by
  cases h with
  | refl hu => exact hu
  | step hu _ _ => exact hu

theorem Reachable.trans {n : Nat} {G : Graph n} {S : Fin n → Bool} {u v w : Fin n}
    (h1 : Reachable G S u v) (h2 : Reachable G S v w) : Reachable G S u w := by
  induction h1 with
  | refl _ => exact h2
  | step hu hadj _ ih => exact Reachable.step hu hadj (ih h2)

theorem Reachable.symm {n : Nat} {G : Graph n} {S : Fin n → Bool} {u v : Fin n}
    (h : Reachable G S u v) : Reachable G S v u := by
  induction h with
  | refl hu => exact Reachable.refl hu
  | step hu hadj hrest ih =>
    have hw : S _ = true := hrest.source_mem
    have hvu : Reachable G S _ _ :=
      Reachable.step hw (by rw [G.symm]; exact hadj) (Reachable.refl hu)
    exact ih.trans hvu

theorem Reachable.mono {n : Nat} {G : Graph n} {S₁ S₂ : Fin n → Bool} {u v : Fin n}
    (hsub : ∀ x, S₁ x = true → S₂ x = true) (h : Reachable G S₁ u v) :
    Reachable G S₂ u v := by
  induction h with
  | refl hu => exact Reachable.refl (hsub _ hu)
  | step hu hadj _ ih => exact Reachable.step (hsub _ hu) hadj ih

def IsConnected {n : Nat} (G : Graph n) (S : Fin n → Bool) : Prop :=
  ∀ u v : Fin n, S u = true → S v = true → Reachable G S u v

def Is2Connected {n : Nat} (G : Graph n) : Prop :=
  3 ≤ n ∧ ∀ v : Fin n, IsConnected G (fun x => x != v)

/-! ## Section 3: Boundary Ordering of a Connected Subgraph (Pillar 1) -/

/-- If `u` can reach `r` in `S`, `u ∉ T`, and `r ∈ T`, then there is a vertex `x`
    with `S x = true`, `x ∉ T`, adjacent to some `y ∈ T` with `S y = true`. -/
theorem exists_boundary_vertex {n : Nat} (G : Graph n) (S : Fin n → Bool)
    (T : List (Fin n)) {u r : Fin n}
    (hreach : Reachable G S u r) (hu : u ∉ T) (hr : r ∈ T) :
    ∃ x, S x = true ∧ x ∉ T ∧ ∃ y ∈ T, S y = true ∧ G.adj x y = true := by
  induction hreach with
  | refl _ => exact absurd hr hu
  | step hsu hadj hrest ih =>
    rename_i a b c
    by_cases hb : b ∈ T
    · exact ⟨a, hsu, hu, b, hb, hrest.source_mem, hadj⟩
    · exact ih hb hr

/-- A valid elimination sequence `T` for `S`: every non-final vertex in `T`
    has a neighbour in `S` appearing strictly after it in `T`. -/
def HasLaterNbr {n : Nat} (G : Graph n) (S : Fin n → Bool) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => (∃ z ∈ y :: rest, S z = true ∧ G.adj x z = true) ∧ HasLaterNbr G S (y :: rest)

theorem hasLaterNbr_cons {n : Nat} {G : Graph n} {S : Fin n → Bool}
    {x : Fin n} {T : List (Fin n)} (hT : T ≠ [])
    (hex : ∃ z ∈ T, S z = true ∧ G.adj x z = true) (hln : HasLaterNbr G S T) :
    HasLaterNbr G S (x :: T) := by
  cases T with
  | nil => exact absurd rfl hT
  | cons y rest => exact ⟨hex, hln⟩

/-- Any connected subgraph `S` containing `r` admits a `Nodup` list `xs ++ [r]`
    that covers `S` and satisfies `HasLaterNbr G S (xs ++ [r])`. -/
theorem exists_elimination_order {n : Nat} (G : Graph n) (S : Fin n → Bool) (r : Fin n)
    (hconn : IsConnected G S) (hr : S r = true) :
    ∃ xs : List (Fin n),
      (xs ++ [r]).Nodup ∧
      (∀ x, x ∈ xs ++ [r] ↔ S x = true) ∧
      HasLaterNbr G S (xs ++ [r]) := by
  suffices h : ∀ (k : Nat) (xs : List (Fin n)),
      (xs ++ [r]).Nodup →
      (∀ x ∈ xs ++ [r], S x = true) →
      HasLaterNbr G S (xs ++ [r]) →
      ((List.finRange n).filter (fun x => S x && !(x ∈ xs ++ [r]))).length ≤ k →
      ∃ xs' : List (Fin n),
        (xs' ++ [r]).Nodup ∧
        (∀ x, x ∈ xs' ++ [r] ↔ S x = true) ∧
        HasLaterNbr G S (xs' ++ [r]) by
    exact h n [] (by simp) (by intro x hx; simp at hx; subst hx; exact hr)
      (by simp [HasLaterNbr]) (by
        have hlen := List.length_filter_le (fun x => S x && !(x ∈ ([] ++ [r]))) (List.finRange n)
        rw [List.length_finRange] at hlen
        exact hlen)
  intro k
  induction k with
  | zero =>
    intro xs hnd hsub hln hrem
    refine ⟨xs, hnd, fun x => ⟨hsub x, fun hsx => ?_⟩, hln⟩
    apply Classical.byContradiction
    intro hxnot
    have hmem : x ∈ (List.finRange n).filter (fun z => S z && !(z ∈ xs ++ [r])) := by
      rw [List.mem_filter]
      exact ⟨List.mem_finRange x, by simp [hsx, hxnot]⟩
    have hpos := List.length_pos_of_mem hmem
    omega
  | succ k ih =>
    intro xs hnd hsub hln hrem
    by_cases hfull : ∀ x, S x = true → x ∈ xs ++ [r]
    · exact ⟨xs, hnd, fun x => ⟨hsub x, hfull x⟩, hln⟩
    · have hex : ∃ u, S u = true ∧ u ∉ xs ++ [r] := by
        apply Classical.byContradiction
        intro hno
        exact hfull (fun x hsx => Classical.byContradiction (fun hnt => hno ⟨x, hsx, hnt⟩))
      obtain ⟨u, hsu, hunot⟩ := hex
      have hrT : r ∈ xs ++ [r] := by simp
      obtain ⟨x, hsx, hxnot, y, hyT, hsy, hadj⟩ :=
        exists_boundary_vertex G S (xs ++ [r]) (hconn u r hsu hr) hunot hrT
      have hnd' : ((x :: xs) ++ [r]).Nodup := List.nodup_cons.mpr ⟨hxnot, hnd⟩
      have hsub' : ∀ z ∈ (x :: xs) ++ [r], S z = true := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzT
        · exact hsx
        · exact hsub z hzT
      have hne : xs ++ [r] ≠ [] := List.append_ne_nil_of_right_ne_nil xs (by simp)
      have hln' : HasLaterNbr G S ((x :: xs) ++ [r]) :=
        hasLaterNbr_cons hne ⟨y, hyT, hsy, hadj⟩ hln
      have hle := nodup_length_le_of_subset
        (x :: (List.finRange n).filter (fun z => S z && !(z ∈ (x :: xs) ++ [r])))
        ((List.finRange n).filter (fun z => S z && !(z ∈ xs ++ [r])))
        (by
          rw [List.nodup_cons]
          refine ⟨?_, (List.nodup_finRange n).filter _⟩
          rw [List.mem_filter]
          intro ⟨_, hcond⟩
          simp at hcond)
        (by
          intro z hz
          rw [List.mem_filter]
          refine ⟨List.mem_finRange z, ?_⟩
          rcases List.mem_cons.mp hz with rfl | hzA
          · simp [hsx, hxnot]
          · rw [List.mem_filter] at hzA
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
              List.cons_append, List.mem_cons, not_or] at hzA ⊢
            exact ⟨hzA.2.1, hzA.2.2.2⟩)
      simp only [List.length_cons] at hle
      exact ih (x :: xs) hnd' hsub' hln' (by omega)

/-! ## Section 4: Deferred Final Block, Greedy Extension, and Proof for d ≥ 4 -/

theorem exists_insertAt_filter {α : Type} (p : α → Bool) (x : α) (L : List α)
    (hp : p x = true) (j : Nat) (hj : j ≤ (L.filter p).length) :
    ∃ i ≤ L.length, (insertAt x i L).filter p = insertAt x j (L.filter p) := by
  induction L generalizing j with
  | nil =>
    simp only [List.filter_nil, List.length_nil] at hj ⊢
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    exact ⟨0, Nat.le_refl 0, by simp [insertAt, hp]⟩
  | cons a L ih =>
    cases j with
    | zero =>
      exact ⟨0, Nat.zero_le _, by simp [insertAt, hp]⟩
    | succ j =>
      cases hpa : p a with
      | true =>
        simp only [List.filter_cons, hpa, List.length_cons] at hj ⊢
        obtain ⟨i, hi, hfilt⟩ := ih j (Nat.le_of_succ_le_succ hj)
        exact ⟨i + 1, Nat.succ_le_succ hi, by simp [insertAt, hpa, hfilt]⟩
      | false =>
        simp only [List.filter_cons, hpa] at hj ⊢
        obtain ⟨i, hi, hfilt⟩ := ih (j + 1) hj
        exact ⟨i + 1, Nat.succ_le_succ hi, by simp [insertAt, hpa, hfilt]⟩

theorem map_insertAt {α β : Type} (f : α → β) (x : α) (j : Nat) (l : List α) :
    (insertAt x j l).map f = insertAt (f x) j (l.map f) := by
  induction j generalizing l with
  | zero => simp [insertAt]
  | succ j ih =>
    cases l with
    | nil => simp [insertAt]
    | cons a l => simp [insertAt, ih]

theorem filter_nodup_singleton {α : Type} (L : List α) (p : α → Bool) (e : α)
    (hnd : L.Nodup) (he : e ∈ L) (hpe : p e = true)
    (huniq : ∀ e' ∈ L, p e' = true → e' = e) :
    L.filter p = [e] := by
  induction L with
  | nil => cases he
  | cons a L ih =>
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | heL
    · simp only [List.filter_cons, hpe]
      have hnil : L.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro e' he' hpe'
        have hEq : e' = e := huniq e' (List.mem_cons_of_mem _ he') hpe'
        exact hnd.1 (hEq ▸ he')
      simp [hnil]
    · have hpa : p a = false := by
        cases hpa' : p a
        · rfl
        · have hae : a = e := huniq a (List.mem_cons_self ..) hpa'
          exact absurd (hae ▸ heL) hnd.1
      simp only [List.filter_cons, hpa]
      exact ih hnd.2 heL (fun e' he' hpe' => huniq e' (List.mem_cons_of_mem _ he') hpe')

theorem mkEdge_inj_left {n : Nat} {v u₁ u₂ : Fin n} (h₁ : v ≠ u₁) (h₂ : v ≠ u₂)
    (heq : mkEdge v u₁ h₁ = mkEdge v u₂ h₂) : u₁ = u₂ := by
  have h1 : (mkEdge v u₁ h₁).incident u₁ = true := (mkEdge_incident v u₁ u₁ h₁).mpr (Or.inr rfl)
  rw [heq, mkEdge_incident] at h1
  rcases h1 with h1 | h1
  · exact absurd h1.symm h₁
  · exact h1

theorem nodup_of_map {α β : Type} (f : α → β) (l : List α)
    (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rw [List.nodup_cons]
    exact ⟨fun ha => h.1 ⟨a, ha, rfl⟩, ih h.2⟩

theorem nodup_attach_of {α : Type} {l : List α} (h : l.Nodup) : l.attach.Nodup :=
  nodup_of_map Subtype.val l.attach (by simpa using h)

theorem nodup_incEdges {n : Nat} (G : Graph n) (v : Fin n) : (G.incEdges v).Nodup := by
  unfold Graph.incEdges
  apply nodup_map_inj
  · exact nodup_attach_of (nodup_nbrs G v)
  · rintro ⟨u₁, hu₁⟩ _ ⟨u₂, hu₂⟩ _ heq
    exact Subtype.ext (mkEdge_inj_left _ _ heq)

/-- Prospective full sequence of vertex `x` given an ordering `L` of edges before the final block
    `B = E_G(v) \ {v u₁}`. -/
def prospSeq {n : Nat} {C : Type} (G : Graph n) (w : Edge n → C) (v u₁ : Fin n)
    (L : List (Edge n)) (x : Fin n) : List C :=
  if h : G.adj v x = true ∧ x ≠ u₁ then
    vertexSeq w L x ++ [w (mkEdge v x (edge_ne_of_adj G h.1))]
  else
    vertexSeq w L x

theorem prospSeq_congr {n : Nat} {C : Type} (G : Graph n) (w : Edge n → C) (v u₁ : Fin n)
    (L₁ L₂ : List (Edge n)) (x : Fin n)
    (h : L₁.filter (fun e => e.incident x) = L₂.filter (fun e => e.incident x)) :
    prospSeq G w v u₁ L₁ x = prospSeq G w v u₁ L₂ x := by
  unfold prospSeq vertexSeq
  rw [h]

/-- Lemma 1 (Final-Block Suffix Invariance). -/
theorem final_block_invariance {n : Nat} {C : Type} (G : Graph n) (w : Edge n → C)
    (v u₁ : Fin n) (hvu1 : G.adj v u₁ = true)
    (L₀ B_ord : List (Edge n))
    (hL₀_nd : L₀.Nodup)
    (hL₀_mem : ∀ e : Edge n, e ∈ L₀ ↔
      e.isEdge G = true ∧ (e.incident v = false ∨ e = mkEdge v u₁ (edge_ne_of_adj G hvu1)))
    (hB_nd : B_ord.Nodup)
    (hB_mem : ∀ e : Edge n, e ∈ B_ord ↔
      e.isEdge G = true ∧ e.incident v = true ∧ e ≠ mkEdge v u₁ (edge_ne_of_adj G hvu1)) :
    IsEdgeOrder G (L₀ ++ B_ord) ∧
    (∀ x : Fin n, x ≠ v → vertexSeq w (L₀ ++ B_ord) x = prospSeq G w v u₁ L₀ x) ∧
    vertexSeq w (L₀ ++ B_ord) v = w (mkEdge v u₁ (edge_ne_of_adj G hvu1)) :: B_ord.map w := by
  let e_vu1 := mkEdge v u₁ (edge_ne_of_adj G hvu1)
  have hord : IsEdgeOrder G (L₀ ++ B_ord) := by
    refine ⟨?_, ?_⟩
    · rw [nodup_append_iff]
      refine ⟨hL₀_nd, hB_nd, fun e heL heB => ?_⟩
      have h1 := (hL₀_mem e).mp heL
      have h2 := (hB_mem e).mp heB
      rcases h1.2 with hfv | heq
      · rw [hfv] at h2; cases h2.2.1
      · exact h2.2.2 heq
    · intro e
      rw [List.mem_append, hL₀_mem, hB_mem]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro he
        cases hv : e.incident v with
        | false => left; exact ⟨he, Or.inl rfl⟩
        | true =>
          by_cases heq : e = e_vu1
          · left; exact ⟨he, Or.inr heq⟩
          · right; exact ⟨he, rfl, heq⟩
  have hx_eq : ∀ x : Fin n, x ≠ v → vertexSeq w (L₀ ++ B_ord) x = prospSeq G w v u₁ L₀ x := by
    intro x hxv
    unfold vertexSeq prospSeq
    rw [List.filter_append, List.map_append]
    split
    · rename_i hcond
      let e_vx := mkEdge v x (edge_ne_of_adj G hcond.1)
      have hevx_mem : e_vx ∈ B_ord := by
        rw [hB_mem]
        refine ⟨by rw [mkEdge_isEdge]; exact hcond.1,
                (mkEdge_incident v x v _).mpr (Or.inl rfl),
                fun heq => hcond.2 (mkEdge_inj_left _ _ heq)⟩
      have hfiltB : B_ord.filter (fun e => e.incident x) = [e_vx] := by
        apply filter_nodup_singleton B_ord (fun e => e.incident x) e_vx hB_nd hevx_mem
        · exact (mkEdge_incident v x x _).mpr (Or.inr rfl)
        · intro e' he' hincx
          have h2 := (hB_mem e').mp he'
          exact edge_eq_mkEdge e' v x h2.2.1 hincx (edge_ne_of_adj G hcond.1)
      rw [hfiltB]
      simp [e_vx, vertexSeq]
    · rename_i hnot
      have hfiltB : B_ord.filter (fun e => e.incident x) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e' he' hincx
        have h2 := (hB_mem e').mp he'
        have heq : e' = mkEdge v x hxv.symm := edge_eq_mkEdge e' v x h2.2.1 hincx hxv.symm
        have hadj : G.adj v x = true := by
          have := h2.1
          rw [heq, mkEdge_isEdge] at this
          exact this
        have hxu1 : x ≠ u₁ := by
          intro hEq
          subst hEq
          exact h2.2.2 heq
        exact hnot ⟨hadj, hxu1⟩
      rw [hfiltB]
      simp [vertexSeq]
  have hv_eq : vertexSeq w (L₀ ++ B_ord) v = w e_vu1 :: B_ord.map w := by
    unfold vertexSeq
    rw [List.filter_append, List.map_append]
    have hfiltL : L₀.filter (fun e => e.incident v) = [e_vu1] := by
      apply filter_nodup_singleton L₀ (fun e => e.incident v) e_vu1 hL₀_nd
      · rw [hL₀_mem]
        exact ⟨by rw [mkEdge_isEdge]; exact hvu1, Or.inr rfl⟩
      · exact (mkEdge_incident v u₁ v _).mpr (Or.inl rfl)
      · intro e' he' hincv
        have h1 := (hL₀_mem e').mp he'
        rcases h1.2 with hfv | heq
        · rw [hfv] at hincv; cases hincv
        · exact heq
    have hfiltB : B_ord.filter (fun e => e.incident v) = B_ord := by
      exact List.filter_eq_self.mpr (fun e he => ((hB_mem e).mp he).2.1)
    rw [hfiltL, hfiltB]
    rfl
  exact ⟨hord, hx_eq, hv_eq⟩

/-- Core pigeonhole insertion step: inserting a single new incident edge `e_star` into `L'`
    at one of `(L'.filter (·.incident x)).length + 1` positions avoids any forbidden list of
    strictly smaller length, without altering any vertex not incident with `e_star`. -/
theorem insert_edge_avoid {n : Nat} {C : Type} [DecidableEq C]
    (G : Graph n) (w : Edge n → C) (hprop : IsProperEdgeColoring G w)
    (v u₁ x : Fin n) (L' : List (Edge n)) (e_star : Edge n)
    (hL'_nd : L'.Nodup)
    (hL'_edge : ∀ e ∈ L', e.isEdge G = true)
    (he_not : e_star ∉ L')
    (he_edge : e_star.isEdge G = true)
    (he_inc : e_star.incident x = true)
    (forb : List (List C))
    (hforb : forb.length < (L'.filter (fun e => e.incident x)).length + 1) :
    ∃ i ≤ L'.length,
      (insertAt e_star i L').Nodup ∧
      prospSeq G w v u₁ (insertAt e_star i L') x ∉ forb ∧
      ∀ z : Fin n, e_star.incident z = false →
        prospSeq G w v u₁ (insertAt e_star i L') z = prospSeq G w v u₁ L' z := by
  let inc := L'.filter (fun e => e.incident x)
  have hcol_not : w e_star ∉ inc.map w := by
    rw [List.mem_map]
    rintro ⟨e, he, hweq⟩
    have heL : e ∈ L' := (List.mem_filter.mp he).1
    have heinc : e.incident x = true := (List.mem_filter.mp he).2
    have hne : e ≠ e_star := fun h => he_not (h ▸ heL)
    exact hprop e e_star (hL'_edge e heL) he_edge hne ⟨x, heinc, he_inc⟩ hweq
  let baseCands := allInserts (w e_star) (inc.map w)
  have hbase_nd : baseCands.Nodup := nodup_allInserts (w e_star) (inc.map w) hcol_not
  have hbase_len : baseCands.length = inc.length + 1 := by
    simp [baseCands, length_allInserts]
  let post : List C → List C :=
    if h : G.adj v x = true ∧ x ≠ u₁ then
      fun s => s ++ [w (mkEdge v x (edge_ne_of_adj G h.1))]
    else
      fun s => s
  have hpost_inj : ∀ s₁ s₂ : List C, post s₁ = post s₂ → s₁ = s₂ := by
    intro s₁ s₂ hEq
    dsimp [post] at hEq
    split at hEq
    · exact (List.append_inj_left' hEq rfl)
    · exact hEq
  let cands := baseCands.map post
  have hcands_nd : cands.Nodup :=
    nodup_map_inj post baseCands hbase_nd (fun _ _ _ _ h => hpost_inj _ _ h)
  have hcands_len : cands.length = inc.length + 1 := by
    simp [cands, hbase_len]
  obtain ⟨c, hc_mem, hc_not⟩ := pigeonhole_list cands forb hcands_nd (by rw [hcands_len]; exact hforb)
  rw [List.mem_map] at hc_mem
  obtain ⟨q, hq_mem, rfl⟩ := hc_mem
  obtain ⟨j, hj, hq_eq⟩ := (mem_allInserts_iff (w e_star) (inc.map w) q).mp hq_mem
  rw [List.length_map] at hj
  obtain ⟨i, hi, hfilt⟩ := exists_insertAt_filter (fun e => e.incident x) e_star L' he_inc j hj
  refine ⟨i, hi, nodup_insertAt e_star i L' hL'_nd he_not, ?_, ?_⟩
  · have hseq : prospSeq G w v u₁ (insertAt e_star i L') x = post q := by
      have hvseq : vertexSeq w (insertAt e_star i L') x = q := by
        unfold vertexSeq
        rw [hfilt, map_insertAt, ← hq_eq]
      unfold prospSeq
      dsimp [post]
      split <;> rw [hvseq]
    rw [hseq]
    exact hc_not
  · intro z hz
    apply prospSeq_congr
    exact filter_insertAt_false (fun e => e.incident z) e_star i L' hz

/-- Lemma 2 (Greedy Extension with Deferred Final Block). -/
theorem greedy_extension {n : Nat} {C : Type} [DecidableEq C]
    (G : Graph n) (w : Edge n → C) (hprop : IsProperEdgeColoring G w)
    (v u₁ : Fin n) (hvu1 : G.adj v u₁ = true)
    (xs : List (Fin n)) :
    ∀ (done : List (Fin n)) (L : List (Edge n)),
      (done ++ xs ++ [u₁]).Nodup →
      (∀ z : Fin n, z ∈ done ++ xs ++ [u₁] ↔ z ≠ v) →
      HasLaterNbr G (fun z => z != v) (xs ++ [u₁]) →
      L.Nodup →
      (∀ e : Edge n, e ∈ L ↔
        e.isEdge G = true ∧ e.incident v = false ∧ ∃ y ∈ done, e.incident y = true) →
      (∀ a ∈ done, ∀ b ∈ done, G.adj a b = true →
        prospSeq G w v u₁ L a ≠ prospSeq G w v u₁ L b) →
      ∃ L₀ : List (Edge n),
        L₀.Nodup ∧
        (∀ e : Edge n, e ∈ L₀ ↔
          e.isEdge G = true ∧ (e.incident v = false ∨ e = mkEdge v u₁ (edge_ne_of_adj G hvu1))) ∧
        (∀ y ∈ done, prospSeq G w v u₁ L₀ y = prospSeq G w v u₁ L y) ∧
        (∀ a b : Fin n, a ≠ v → b ≠ v → G.adj a b = true →
          prospSeq G w v u₁ L₀ a ≠ prospSeq G w v u₁ L₀ b) := by
  induction xs with
  | nil =>
    intro done L hnd_all hcov _ hL_nd hL_mem hdist
    -- Every edge of H = G - v is already in L
    have hL_allH : ∀ e : Edge n, e ∈ L ↔ e.isEdge G = true ∧ e.incident v = false := by
      intro e
      rw [hL_mem]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, h2, ?_⟩
        have hne : e.u ≠ e.v := fun h => by have := e.hlt; rw [h] at this; exact Nat.lt_irrefl _ this
        have huv : e.u ≠ v := by
          intro h; subst h
          have : e.incident e.u = true := by simp [Edge.incident]
          rw [this] at h2; cases h2
        have hvv : e.v ≠ v := by
          intro h; subst h
          have : e.incident e.v = true := by simp [Edge.incident]
          rw [this] at h2; cases h2
        have hu_mem : e.u ∈ done ++ [] ++ [u₁] := (hcov e.u).mpr huv
        have hv_mem : e.v ∈ done ++ [] ++ [u₁] := (hcov e.v).mpr hvv
        simp only [List.append_nil, List.mem_append, List.mem_singleton] at hu_mem hv_mem
        rcases hu_mem with huD | hu1eq
        · exact ⟨e.u, huD, by simp [Edge.incident]⟩
        · rcases hv_mem with hvD | hv1eq
          · exact ⟨e.v, hvD, by simp [Edge.incident]⟩
          · exact absurd (hu1eq.trans hv1eq.symm) hne
    -- Insert e_vu1 into L to distinguish u₁ from its neighbours in H
    let e_vu1 := mkEdge v u₁ (edge_ne_of_adj G hvu1)
    have he_not : e_vu1 ∉ L := by
      intro hm
      have h2 := ((hL_allH e_vu1).mp hm).2
      have h1 : e_vu1.incident v = true := (mkEdge_incident v u₁ v _).mpr (Or.inl rfl)
      rw [h1] at h2; cases h2
    have he_edge : e_vu1.isEdge G = true := by rw [mkEdge_isEdge]; exact hvu1
    have he_inc : e_vu1.incident u₁ = true := (mkEdge_incident v u₁ u₁ _).mpr (Or.inr rfl)
    let nbrsH := (G.nbrs u₁).filter (fun y => y != v)
    let forb := nbrsH.map (prospSeq G w v u₁ L)
    -- Every neighbour y ∈ nbrsH gives a distinct edge mkEdge u₁ y _ in L.filter (·.incident u₁)
    have hlen_le : nbrsH.length ≤ (L.filter (fun e => e.incident u₁)).length := by
      let edgesH := nbrsH.attach.map (fun ⟨y, hy⟩ =>
        mkEdge u₁ y (edge_ne_of_adj G ((mem_nbrs G u₁ y).mp (List.mem_filter.mp hy).1)))
      have hedges_nd : edgesH.Nodup := by
        apply nodup_map_inj
        · exact nodup_attach_of ((nodup_nbrs G u₁).filter _)
        · rintro ⟨y₁, _⟩ _ ⟨y₂, _⟩ _ hEq
          exact Subtype.ext (mkEdge_inj_left _ _ hEq)
      have hsub : ∀ e ∈ edgesH, e ∈ L.filter (fun e => e.incident u₁) := by
        intro e he
        rw [List.mem_map] at he
        obtain ⟨⟨y, hy⟩, _, rfl⟩ := he
        have hy_adj : G.adj u₁ y = true := (mem_nbrs G u₁ y).mp (List.mem_filter.mp hy).1
        have hyv : y ≠ v := bne_iff_ne.mp (List.mem_filter.mp hy).2
        have hu1v : u₁ ≠ v := (edge_ne_of_adj G hvu1).symm
        rw [List.mem_filter]
        refine ⟨(hL_allH _).mpr ⟨by rw [mkEdge_isEdge]; exact hy_adj, ?_⟩,
                (mkEdge_incident u₁ y u₁ _).mpr (Or.inl rfl)⟩
        cases hincv : (mkEdge u₁ y _).incident v with
        | false => rfl
        | true =>
          rw [mkEdge_incident] at hincv
          rcases hincv with hEq | hEq
          · exact absurd hEq.symm hu1v
          · exact absurd hEq.symm hyv
      have hle := nodup_length_le_of_subset edgesH (L.filter (fun e => e.incident u₁)) hedges_nd hsub
      simpa [edgesH] using hle
    have hforb_lt : forb.length < (L.filter (fun e => e.incident u₁)).length + 1 := by
      simp only [forb, List.length_map]
      omega
    obtain ⟨i, _, hnd_ins, hnot_forb, hpres⟩ :=
      insert_edge_avoid G w hprop v u₁ u₁ L e_vu1 hL_nd
        (fun e he => ((hL_allH e).mp he).1) he_not he_edge he_inc forb hforb_lt
    refine ⟨insertAt e_vu1 i L, hnd_ins, ?_, ?_, ?_⟩
    · intro e
      rw [mem_insertAt, hL_allH]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨he_edge, Or.inr rfl⟩
        · exact ⟨h1, Or.inl h2⟩
      · rintro ⟨h1, h2 | rfl⟩
        · right; exact ⟨h1, h2⟩
        · left; rfl
    · intro y hy
      have hyu1 : y ≠ u₁ := by
        intro hEq; subst hEq
        simp only [List.append_nil] at hnd_all
        rw [nodup_append_iff] at hnd_all
        exact hnd_all.2.2 y hy (List.mem_singleton_self y)
      have hyv : y ≠ v := (hcov y).mp (by simp [hy])
      have hnoinc : e_vu1.incident y = false := by
        cases hinc : e_vu1.incident y with
        | false => rfl
        | true =>
          rw [mkEdge_incident] at hinc
          rcases hinc with rfl | rfl
          · exact absurd rfl hyv
          · exact absurd rfl hyu1
      exact hpres y hnoinc
    · intro a b hav hbv hab
      have hpres_not_u1 : ∀ z : Fin n, z ≠ v → z ≠ u₁ →
          prospSeq G w v u₁ (insertAt e_vu1 i L) z = prospSeq G w v u₁ L z := by
        intro z hzv hzu1
        apply hpres
        cases hinc : e_vu1.incident z with
        | false => rfl
        | true =>
          rw [mkEdge_incident] at hinc
          rcases hinc with rfl | rfl
          · exact absurd rfl hzv
          · exact absurd rfl hzu1
      have hdone_of : ∀ z : Fin n, z ≠ v → z ≠ u₁ → z ∈ done := by
        intro z hzv hzu1
        have hz := (hcov z).mpr hzv
        simp only [List.append_nil, List.mem_append, List.mem_singleton] at hz
        exact hz.resolve_right hzu1
      by_cases hau1 : a = u₁
      · subst a
        have hbu1 : b ≠ u₁ := (edge_ne_of_adj G hab).symm
        rw [hpres_not_u1 b hbv hbu1]
        intro hEq
        apply hnot_forb
        rw [hEq]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨(mem_nbrs G u₁ b).mpr hab, bne_iff_ne.mpr hbv⟩, rfl⟩
      · by_cases hbu1 : b = u₁
        · subst b
          rw [hpres_not_u1 a hav hau1]
          intro hEq
          apply hnot_forb
          rw [← hEq]
          have hba : G.adj u₁ a = true := by rw [G.symm]; exact hab
          exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨(mem_nbrs G u₁ a).mpr hba, bne_iff_ne.mpr hav⟩, rfl⟩
        · rw [hpres_not_u1 a hav hau1, hpres_not_u1 b hbv hbu1]
          exact hdist a (hdone_of a hav hau1) b (hdone_of b hbv hbu1) hab
  | cons x xs ih =>
    intro done L hnd_all hcov hln hL_nd hL_mem hdist
    -- Extract a later neighbour `y ∈ xs ++ [u₁]` of `x`
    have hrest_ne : xs ++ [u₁] ≠ [] := List.append_ne_nil_of_right_ne_nil xs (by simp)
    have hlat : (∃ y ∈ xs ++ [u₁], (y != v) = true ∧ G.adj x y = true) ∧
        HasLaterNbr G (fun z => z != v) (xs ++ [u₁]) := by
      cases hxs : xs ++ [u₁] with
      | nil => exact absurd hxs hrest_ne
      | cons w rest =>
        simp only [List.cons_append, hxs] at hln
        exact hln
    obtain ⟨⟨y, hy_rest, hyv_b, hxy⟩, hln_rest⟩ := hlat
    have hyv : y ≠ v := bne_iff_ne.mp hyv_b
    have hxv : x ≠ v := (hcov x).mp (by simp)
    have hnd_split : done.Nodup ∧ (x :: (xs ++ [u₁])).Nodup ∧ ∀ z ∈ done, z ∉ x :: (xs ++ [u₁]) := by
      have h' := hnd_all
      rw [List.append_assoc, List.cons_append, nodup_append_iff] at h'
      exact h'
    have hx_not_done : x ∉ done := fun hx => hnd_split.2.2 x hx (List.mem_cons_self ..)
    have hy_not_done : y ∉ done := fun hy => hnd_split.2.2 y hy (List.mem_cons_of_mem _ hy_rest)
    let e_star := mkEdge x y (edge_ne_of_adj G hxy)
    have he_star_edge : e_star.isEdge G = true := by rw [mkEdge_isEdge]; exact hxy
    have he_star_incx : e_star.incident x = true := (mkEdge_incident x y x _).mpr (Or.inl rfl)
    have he_star_nov : e_star.incident v = false := by
      cases h : e_star.incident v with
      | false => rfl
      | true =>
        rw [mkEdge_incident] at h
        rcases h with rfl | rfl
        · exact absurd rfl hxv
        · exact absurd rfl hyv
    have he_star_not_done : ∀ z ∈ done, e_star.incident z = false := by
      intro z hz
      cases h : e_star.incident z with
      | false => rfl
      | true =>
        rw [mkEdge_incident] at h
        rcases h with rfl | rfl
        · exact absurd hz hx_not_done
        · exact absurd hz hy_not_done
    have he_star_not_L : e_star ∉ L := by
      intro hm
      obtain ⟨_, _, z, hz, hincz⟩ := (hL_mem e_star).mp hm
      rw [he_star_not_done z hz] at hincz; cases hincz
    -- Append all unordered edges of H incident with x except e_star
    let U_rest := (G.incEdges x).filter (fun e => e.incident v == false && !(e ∈ L) && (e != e_star))
    let L' := L ++ U_rest
    have hL'_nd : L'.Nodup := by
      rw [nodup_append_iff]
      refine ⟨hL_nd, (nodup_incEdges G x).filter _, fun e heL heU => ?_⟩
      have hcond := (List.mem_filter.mp heU).2
      simp [heL] at hcond
    have hL'_edge : ∀ e ∈ L', e.isEdge G = true := by
      intro e he
      rcases List.mem_append.mp he with heL | heU
      · exact ((hL_mem e).mp heL).1
      · exact (mem_incEdges G x e).mp (List.mem_filter.mp heU).1 |>.1
    have he_star_not_L' : e_star ∉ L' := by
      rw [List.mem_append, not_or]
      refine ⟨he_star_not_L, fun heU => ?_⟩
      have hcond := (List.mem_filter.mp heU).2
      simp at hcond
    -- No edge of U_rest is incident with any z ∈ done
    have hU_not_done : ∀ e ∈ U_rest, ∀ z ∈ done, e.incident z = false := by
      intro e heU z hz
      cases hinc : e.incident z with
      | false => rfl
      | true =>
        have hmem_inc := (List.mem_filter.mp heU).1
        have hcond := (List.mem_filter.mp heU).2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
          decide_eq_false_iff_not, bne_iff_ne] at hcond
        have he_in_L : e ∈ L := (hL_mem e).mpr ⟨((mem_incEdges G x e).mp hmem_inc).1, hcond.1.1, z, hz, hinc⟩
        exact absurd he_in_L hcond.1.2
    have hL'_pres_done : ∀ z ∈ done, prospSeq G w v u₁ L' z = prospSeq G w v u₁ L z := by
      intro z hz
      apply prospSeq_congr
      rw [List.filter_append]
      have hnil : U_rest.filter (fun e => e.incident z) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e heU hinc
        rw [hU_not_done e heU z hz] at hinc; cases hinc
      rw [hnil, List.append_nil]
    -- Count: (nbrs x in done).length < (L'.filter (·.incident x)).length + 1
    let nbrsH := (G.nbrs x).filter (fun z => z != v)
    let nbrsDone := (G.nbrs x).filter (fun z => z ∈ done)
    have hdone_lt_nbrsH : nbrsDone.length < nbrsH.length := by
      have hnd_y : (y :: nbrsDone).Nodup := by
        rw [List.nodup_cons]
        refine ⟨?_, (nodup_nbrs G x).filter _⟩
        intro hm
        have := (List.mem_filter.mp hm).2
        simp [hy_not_done] at this
      have hsub : ∀ z ∈ y :: nbrsDone, z ∈ nbrsH := by
        intro z hz
        rcases List.mem_cons.mp hz with hzy | hzD
        · rw [hzy]; exact List.mem_filter.mpr ⟨(mem_nbrs G x y).mpr hxy, hyv_b⟩
        · have hz_n := (List.mem_filter.mp hzD).1
          have hz_d : z ∈ done := by simpa using (List.mem_filter.mp hzD).2
          have hzv : z ≠ v := (hcov z).mp (by simp [hz_d])
          exact List.mem_filter.mpr ⟨hz_n, bne_iff_ne.mpr hzv⟩
      have hle := nodup_length_le_of_subset (y :: nbrsDone) nbrsH hnd_y hsub
      simp only [List.length_cons] at hle
      omega
    have hnbrsH_le_inc : nbrsH.length ≤ (L'.filter (fun e => e.incident x)).length + 1 := by
      let edgesH := nbrsH.attach.map (fun ⟨z, hz⟩ =>
        mkEdge x z (edge_ne_of_adj G ((mem_nbrs G x z).mp (List.mem_filter.mp hz).1)))
      have hedges_nd : edgesH.Nodup := by
        apply nodup_map_inj
        · exact nodup_attach_of ((nodup_nbrs G x).filter _)
        · rintro ⟨z₁, _⟩ _ ⟨z₂, _⟩ _ hEq
          exact Subtype.ext (mkEdge_inj_left _ _ hEq)
      have hsub : ∀ e ∈ edgesH, e ∈ e_star :: L'.filter (fun e => e.incident x) := by
        intro e he
        rw [List.mem_map] at he
        obtain ⟨⟨z, hz⟩, _, rfl⟩ := he
        have hz_adj : G.adj x z = true := (mem_nbrs G x z).mp (List.mem_filter.mp hz).1
        have hzv : z ≠ v := bne_iff_ne.mp (List.mem_filter.mp hz).2
        let ez := mkEdge x z (edge_ne_of_adj G hz_adj)
        by_cases heq : ez = e_star
        · exact List.mem_cons.mpr (Or.inl heq)
        · apply List.mem_cons.mpr
          right
          dsimp only
          rw [List.mem_filter]
          refine ⟨?_, (mkEdge_incident x z x _).mpr (Or.inl rfl)⟩
          by_cases hmemL : ez ∈ L
          · exact List.mem_append.mpr (Or.inl hmemL)
          · apply List.mem_append.mpr
            right
            rw [List.mem_filter]
            refine ⟨(mem_incEdges G x ez).mpr ⟨by rw [mkEdge_isEdge]; exact hz_adj,
                      (mkEdge_incident x z x _).mpr (Or.inl rfl)⟩, ?_⟩
            have hnov : ez.incident v = false := by
              cases h : ez.incident v with
              | false => rfl
              | true =>
                dsimp only [ez] at h
                rw [mkEdge_incident] at h
                rcases h with rfl | rfl
                · exact absurd rfl hxv
                · exact absurd rfl hzv
            simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
              decide_eq_false_iff_not, bne_iff_ne]
            exact ⟨⟨hnov, hmemL⟩, heq⟩
      have hle := nodup_length_le_of_subset edgesH (e_star :: L'.filter (fun e => e.incident x)) hedges_nd hsub
      simpa [edgesH] using hle
    let forb := nbrsDone.map (prospSeq G w v u₁ L')
    have hforb_lt : forb.length < (L'.filter (fun e => e.incident x)).length + 1 := by
      simp only [forb, List.length_map]
      omega
    obtain ⟨i, _, hnd_next, hnot_forb, hpres_ins⟩ :=
      insert_edge_avoid G w hprop v u₁ x L' e_star hL'_nd hL'_edge
        he_star_not_L' he_star_edge he_star_incx forb hforb_lt
    let L_next := insertAt e_star i L'
    have hpres_done : ∀ z ∈ done, prospSeq G w v u₁ L_next z = prospSeq G w v u₁ L z := by
      intro z hz
      rw [hpres_ins z (he_star_not_done z hz), hL'_pres_done z hz]
    -- Verify invariants for `done ++ [x]` and `L_next`
    have hnd_next_all : ((done ++ [x]) ++ xs ++ [u₁]).Nodup := by
      simpa [List.append_assoc] using hnd_all
    have hcov_next : ∀ z : Fin n, z ∈ (done ++ [x]) ++ xs ++ [u₁] ↔ z ≠ v := by
      intro z
      simpa [List.append_assoc] using hcov z
    have hL_next_mem : ∀ e : Edge n, e ∈ L_next ↔
        e.isEdge G = true ∧ e.incident v = false ∧ ∃ z ∈ done ++ [x], e.incident z = true := by
      intro e
      simp only [L_next, mem_insertAt, L', List.mem_append, U_rest, List.mem_filter,
        mem_incEdges, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, bne_iff_ne]
      constructor
      · rintro (rfl | heL | ⟨⟨he_g, he_x⟩, ⟨he_v, _⟩, _⟩)
        · exact ⟨he_star_edge, he_star_nov, x, Or.inr (List.mem_singleton_self x), he_star_incx⟩
        · obtain ⟨h1, h2, z, hz, h3⟩ := (hL_mem e).mp heL
          exact ⟨h1, h2, z, Or.inl hz, h3⟩
        · exact ⟨he_g, he_v, x, Or.inr (List.mem_singleton_self x), he_x⟩
      · rintro ⟨h1, h2, z, hz, h3⟩
        rcases hz with hzD | hzx
        · right; left; exact (hL_mem e).mpr ⟨h1, h2, z, hzD, h3⟩
        · have hzx' : z = x := List.mem_singleton.mp hzx
          subst z
          by_cases heq : e = e_star
          · left; exact heq
          · by_cases hmL : e ∈ L
            · right; left; exact hmL
            · right; right; exact ⟨⟨h1, h3⟩, ⟨h2, hmL⟩, heq⟩
    have hdist_next : ∀ a ∈ done ++ [x], ∀ b ∈ done ++ [x], G.adj a b = true →
        prospSeq G w v u₁ L_next a ≠ prospSeq G w v u₁ L_next b := by
      intro a ha b hb hab
      rcases List.mem_append.mp ha with haD | hax <;>
      rcases List.mem_append.mp hb with hbD | hbx
      · rw [hpres_done a haD, hpres_done b hbD]
        exact hdist a haD b hbD hab
      · have hbx' : b = x := List.mem_singleton.mp hbx; subst b
        rw [hpres_ins a (he_star_not_done a haD)]
        intro hEq
        apply hnot_forb
        rw [← hEq]
        have hxa : G.adj x a = true := by rw [G.symm]; exact hab
        exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨(mem_nbrs G x a).mpr hxa, by simp [haD]⟩, rfl⟩
      · have hax' : a = x := List.mem_singleton.mp hax; subst a
        rw [hpres_ins b (he_star_not_done b hbD)]
        intro hEq
        apply hnot_forb
        rw [hEq]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨(mem_nbrs G x b).mpr hab, by simp [hbD]⟩, rfl⟩
      · have hax' : a = x := List.mem_singleton.mp hax
        have hbx' : b = x := List.mem_singleton.mp hbx
        subst a; subst b
        rw [G.loopless] at hab; cases hab
    obtain ⟨L₀, hL₀_nd, hL₀_mem, hL₀_pres, hL₀_dist⟩ :=
      ih (done ++ [x]) L_next hnd_next_all hcov_next hln_rest hnd_next hL_next_mem hdist_next
    refine ⟨L₀, hL₀_nd, hL₀_mem, ?_, hL₀_dist⟩
    intro z hz
    rw [hL₀_pres z (List.mem_append.mpr (Or.inl hz)), hpres_done z hz]

/-- Proof of Theorem A for every `d ≥ 4` (works for any proper edge colouring `w`). -/
theorem theorem_regular_ge_4 {n d : Nat} {C : Type} [DecidableEq C]
    (G : Graph n) (w : Edge n → C)
    (hd : 4 ≤ d) (h2 : Is2Connected G) (hreg : G.IsRegular d)
    (hprop : IsProperEdgeColoring G w) :
    SequentiallyOrderable G w := by
  have hn : 3 ≤ n := h2.1
  let v : Fin n := ⟨0, by omega⟩
  have hdegv : (G.nbrs v).length = d := hreg v
  have hnbrs_ne : G.nbrs v ≠ [] := by
    intro hnil
    rw [hnil] at hdegv
    simp at hdegv; omega
  obtain ⟨u₁, rest_nbrs, hnbrs_eq⟩ := List.exists_cons_of_ne_nil hnbrs_ne
  have hu1_mem : u₁ ∈ G.nbrs v := by rw [hnbrs_eq]; exact List.mem_cons_self ..
  have hvu1 : G.adj v u₁ = true := (mem_nbrs G v u₁).mp hu1_mem
  have hu1v : u₁ ≠ v := (edge_ne_of_adj G hvu1).symm
  -- Elimination order of H = G - v rooted at u₁
  obtain ⟨xs, hxs_nd, hxs_cov, hxs_ln⟩ :=
    exists_elimination_order G (fun x => x != v) u₁ (h2.2 v) (bne_iff_ne.mpr hu1v)
  have hcov' : ∀ z : Fin n, z ∈ [] ++ xs ++ [u₁] ↔ z ≠ v := by
    intro z
    simp only [List.nil_append]
    rw [hxs_cov z, bne_iff_ne]
  obtain ⟨L₀, hL₀_nd, hL₀_mem, _, hL₀_dist⟩ :=
    greedy_extension G w hprop v u₁ hvu1 xs [] []
      (by simpa using hxs_nd) hcov' hxs_ln List.nodup_nil
      (by intro e; simp) (by intro a ha; cases ha)
  -- Final block B_list = edges from v to rest_nbrs
  have hnd_v : (u₁ :: rest_nbrs).Nodup := by rw [← hnbrs_eq]; exact nodup_nbrs G v
  rw [List.nodup_cons] at hnd_v
  have hrest_len : rest_nbrs.length = d - 1 := by
    rw [hnbrs_eq, List.length_cons] at hdegv; omega
  let B_list : List (Edge n) := rest_nbrs.attach.map (fun ⟨u, hu⟩ =>
    mkEdge v u (edge_ne_of_adj G ((mem_nbrs G v u).mp (by rw [hnbrs_eq]; exact List.mem_cons_of_mem _ hu))))
  have hB_list_nd : B_list.Nodup := by
    apply nodup_map_inj
    · exact nodup_attach_of hnd_v.2
    · rintro ⟨a, _⟩ _ ⟨b, _⟩ _ hEq
      exact Subtype.ext (mkEdge_inj_left _ _ hEq)
  have hB_list_len : B_list.length = d - 1 := by
    simp [B_list, hrest_len]
  have hB_list_mem : ∀ e : Edge n, e ∈ B_list ↔
      e.isEdge G = true ∧ e.incident v = true ∧ e ≠ mkEdge v u₁ (edge_ne_of_adj G hvu1) := by
    intro e
    simp only [B_list, List.mem_map, List.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu_nbr : u ∈ G.nbrs v := by rw [hnbrs_eq]; exact List.mem_cons_of_mem _ hu
      have hadj : G.adj v u = true := (mem_nbrs G v u).mp hu_nbr
      refine ⟨by rw [mkEdge_isEdge]; exact hadj,
              (mkEdge_incident v u v _).mpr (Or.inl rfl),
              fun hEq => hnd_v.1 ((mkEdge_inj_left _ _ hEq) ▸ hu)⟩
    · rintro ⟨he, hinc, hne⟩
      have he_mem : e ∈ G.incEdges v := (mem_incEdges G v e).mpr ⟨he, hinc⟩
      unfold Graph.incEdges at he_mem
      rw [List.mem_map] at he_mem
      obtain ⟨⟨u, hu⟩, _, rfl⟩ := he_mem
      have hu' : u ∈ u₁ :: rest_nbrs := by rw [← hnbrs_eq]; exact hu
      rcases List.mem_cons.mp hu' with rfl | hurest
      · exact absurd rfl hne
      · exact ⟨u, hurest, rfl⟩
  -- w is injective on B_list
  have hw_inj : ∀ e₁ ∈ B_list, ∀ e₂ ∈ B_list, w e₁ = w e₂ → e₁ = e₂ := by
    intro e₁ h1 e₂ h2 hweq
    apply Classical.byContradiction
    intro hne
    have h1' := (hB_list_mem e₁).mp h1
    have h2' := (hB_list_mem e₂).mp h2
    exact hprop e₁ e₂ h1'.1 h2'.1 hne ⟨v, h1'.2.1, h2'.2.1⟩ hweq
  -- Candidate sequences for v from all (d - 1)! permutations of B_list
  let e_vu1 := mkEdge v u₁ (edge_ne_of_adj G hvu1)
  let seqOfB : List (Edge n) → List C := fun B_ord => w e_vu1 :: B_ord.map w
  let cands := (perms B_list).map seqOfB
  have hcands_nd : cands.Nodup := by
    apply nodup_map_inj seqOfB (perms B_list) (nodup_perms B_list hB_list_nd)
    intro B₁ hB₁ B₂ hB₂ hEq
    simp only [seqOfB, List.cons.injEq] at hEq
    have hsub1 : ∀ e ∈ B₁, e ∈ B_list := fun e he => (perms_perm B_list B₁ hB₁).subset he
    have hsub2 : ∀ e ∈ B₂, e ∈ B_list := fun e he => (perms_perm B_list B₂ hB₂).subset he
    -- map w injective on lists of elements from B_list
    have hmap_inj : ∀ (l₁ l₂ : List (Edge n)),
        (∀ e ∈ l₁, e ∈ B_list) → (∀ e ∈ l₂, e ∈ B_list) → l₁.map w = l₂.map w → l₁ = l₂ := by
      intro l₁
      induction l₁ with
      | nil =>
        intro l₂ _ _ h; cases l₂ with
        | nil => rfl
        | cons _ _ => simp at h
      | cons a l₁ ihl =>
        intro l₂ hs1 hs2 h
        cases l₂ with
        | nil => simp at h
        | cons b l₂ =>
          simp only [List.map_cons, List.cons.injEq] at h
          have hab : a = b := hw_inj a (hs1 a (List.mem_cons_self ..)) b (hs2 b (List.mem_cons_self ..)) h.1
          rw [hab, ihl l₂ (fun e he => hs1 e (List.mem_cons_of_mem _ he))
            (fun e he => hs2 e (List.mem_cons_of_mem _ he)) h.2]
    exact hmap_inj B₁ B₂ hsub1 hsub2 hEq.2
  let forb := (G.nbrs v).map (prospSeq G w v u₁ L₀)
  have hlt : forb.length < cands.length := by
    simp only [forb, cands, List.length_map, length_perms, hB_list_len, hdegv]
    exact lt_fact_pred d hd
  obtain ⟨c, hc_mem, hc_not⟩ := pigeonhole_list cands forb hcands_nd hlt
  rw [List.mem_map] at hc_mem
  obtain ⟨B_ord, hB_ord_mem, rfl⟩ := hc_mem
  have hB_perm := perms_perm B_list B_ord hB_ord_mem
  have hB_ord_nd : B_ord.Nodup := hB_perm.nodup_iff.mpr hB_list_nd
  have hB_ord_cov : ∀ e : Edge n, e ∈ B_ord ↔
      e.isEdge G = true ∧ e.incident v = true ∧ e ≠ e_vu1 := by
    intro e
    rw [hB_perm.mem_iff, hB_list_mem]
  obtain ⟨hord, hx_eq, hv_eq⟩ :=
    final_block_invariance G w v u₁ hvu1 L₀ B_ord hL₀_nd hL₀_mem hB_ord_nd hB_ord_cov
  refine ⟨L₀ ++ B_ord, hord, ?_⟩
  intro a b hab
  by_cases hav : a = v
  · subst a
    have hbv : b ≠ v := (edge_ne_of_adj G hab).symm
    rw [hv_eq, hx_eq b hbv]
    intro hEq
    apply hc_not
    dsimp only [seqOfB, e_vu1]
    rw [hEq]
    exact List.mem_map.mpr ⟨b, (mem_nbrs G v b).mpr hab, rfl⟩
  · by_cases hbv : b = v
    · subst b
      rw [hv_eq, hx_eq a hav]
      intro hEq
      apply hc_not
      dsimp only [seqOfB, e_vu1]
      rw [← hEq]
      have hva : G.adj v a = true := by rw [G.symm]; exact hab
      exact List.mem_map.mpr ⟨a, (mem_nbrs G v a).mpr hva, rfl⟩
    · rw [hx_eq a hav, hx_eq b hbv]
      exact hL₀_dist a b hav hbv hab

/-! ## Section 5: Non-Separating P₃ Lemma (Lemma 3) and Proof for d = 3 -/

section Cubic

open Classical

/-- Cardinality of a boolean vertex predicate on `Fin n`. -/
def countS {n : Nat} (S : Fin n → Bool) : Nat :=
  ((List.finRange n).filter S).length

theorem countS_pos_of_true {n : Nat} {S : Fin n → Bool} {x : Fin n} (hx : S x = true) :
    0 < countS S :=
  List.length_pos_of_mem (List.mem_filter.mpr ⟨List.mem_finRange x, hx⟩)

theorem countS_lt_of_ssub {n : Nat} {S₁ S₂ : Fin n → Bool}
    (hsub : ∀ z, S₁ z = true → S₂ z = true) {x : Fin n}
    (h1 : S₁ x = false) (h2 : S₂ x = true) :
    countS S₁ < countS S₂ := by
  have hnd : (x :: (List.finRange n).filter S₁).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, (List.nodup_finRange n).filter _⟩
    intro hm
    have := (List.mem_filter.mp hm).2
    rw [h1] at this; cases this
  have hs : ∀ z ∈ x :: (List.finRange n).filter S₁, z ∈ (List.finRange n).filter S₂ := by
    intro z hz
    rw [List.mem_filter]
    refine ⟨List.mem_finRange z, ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz1
    · exact h2
    · exact hsub z (List.mem_filter.mp hz1).2
  have hle := nodup_length_le_of_subset _ _ hnd hs
  simp only [List.length_cons] at hle
  exact hle

/-- If `l₁` is a nodup list of length `k` inside a nodup list `l₂` of length `k`,
    then every element of `l₂` belongs to `l₁`. -/
theorem mem_of_nodup_subset_eq_len {α : Type} [DecidableEq α]
    (l₁ l₂ : List α) (hnd1 : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂)
    (hlen : l₁.length = l₂.length) {y : α} (hy : y ∈ l₂) : y ∈ l₁ := by
  apply Classical.byContradiction
  intro hnot
  have hnd' : (y :: l₁).Nodup := List.nodup_cons.mpr ⟨hnot, hnd1⟩
  have hsub' : ∀ x ∈ y :: l₁, x ∈ l₂ := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx1
    · exact hy
    · exact hsub x hx1
  have hle := nodup_length_le_of_subset (y :: l₁) l₂ hnd' hsub'
  simp only [List.length_cons] at hle
  omega

/-- If a vertex `x` has degree 3 and three distinct neighbours `p, q, r`,
    then every neighbour of `x` is one of `p, q, r`. -/
theorem nbr_eq_of_three_nbrs {n : Nat} (G : Graph n) (hreg : G.IsRegular 3)
    {x p q r : Fin n}
    (hp : G.adj x p = true) (hq : G.adj x q = true) (hr : G.adj x r = true)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {y : Fin n} (hy : G.adj x y = true) :
    y = p ∨ y = q ∨ y = r := by
  have hnd : ([p, q, r] : List (Fin n)).Nodup := by
    simp [hpq, hpr, hqr]
  have hsub : ∀ z ∈ ([p, q, r] : List (Fin n)), z ∈ G.nbrs x := by
    intro z hz
    rw [mem_nbrs]
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hp
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hq
      · have hzr := List.mem_singleton.mp hz; subst hzr; exact hr
  have hlen : ([p, q, r] : List (Fin n)).length = (G.nbrs x).length := by
    show 3 = G.deg x
    exact (hreg x).symm
  have hmem := mem_of_nodup_subset_eq_len [p, q, r] (G.nbrs x) hnd hsub hlen ((mem_nbrs G x y).mpr hy)
  simpa using hmem

/-- A degree-3 vertex cannot have 4 pairwise distinct neighbours. -/
theorem not_four_nbrs {n : Nat} (G : Graph n) (hreg : G.IsRegular 3)
    {x p q r s : Fin n}
    (hp : G.adj x p = true) (hq : G.adj x q = true) (hr : G.adj x r = true) (hs : G.adj x s = true)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    False := by
  rcases nbr_eq_of_three_nbrs G hreg hp hq hr hpq hpr hqr hs with h | h | h
  · exact hps h.symm
  · exact hqs h.symm
  · exact hrs h.symm

/-- A degree-3 vertex with two distinct neighbours `p, q` has a third neighbour `r ∉ {p, q}`. -/
theorem exists_third_nbr {n : Nat} (G : Graph n) (hreg : G.IsRegular 3)
    {x p q : Fin n} :
    ∃ r : Fin n, G.adj x r = true ∧ r ≠ p ∧ r ≠ q := by
  have hlt : ([p, q] : List (Fin n)).length < (G.nbrs x).length := by
    have : (G.nbrs x).length = 3 := hreg x
    simp [this]
  obtain ⟨r, hr_mem, hr_not⟩ := pigeonhole_list (G.nbrs x) [p, q] (nodup_nbrs G x) hlt
  simp only [List.mem_cons, not_or] at hr_not
  exact ⟨r, (mem_nbrs G x r).mp hr_mem, hr_not.1, hr_not.2.1⟩

/-- If `Q` is closed under edges inside `S`, then `Reachable G S x y` and `Q x = true` imply `Q y = true`. -/
theorem reachable_stays_in_closed {n : Nat} (G : Graph n) (S Q : Fin n → Bool)
    (hclosed : ∀ a b, S a = true → S b = true → Q a = true → G.adj a b = true → Q b = true)
    {x y : Fin n} (hreach : Reachable G S x y) (hx : Q x = true) :
    Q y = true := by
  induction hreach with
  | refl _ => exact hx
  | step hsa hadj hrest ih =>
    exact ih (hclosed _ _ hsa hrest.source_mem hx hadj)

/-- A 2-connected graph is connected. -/
theorem isConnected_all_of_2connected {n : Nat} (G : Graph n) (h2 : Is2Connected G) :
    IsConnected G (fun _ => true) := by
  intro u v _ _
  have hn : 3 ≤ n := h2.1
  -- Pick a vertex `z ∉ {u, v}`
  have hlt : ([u, v] : List (Fin n)).length < (List.finRange n).length := by
    simp; omega
  obtain ⟨z, _, hz_not⟩ := pigeonhole_list (List.finRange n) [u, v] (List.nodup_finRange n) hlt
  simp only [List.mem_cons, not_or] at hz_not
  have hr := h2.2 z u v (bne_iff_ne.mpr (Ne.symm hz_not.1)) (bne_iff_ne.mpr (Ne.symm hz_not.2.1))
  exact hr.mono (fun _ _ => rfl)

/-- A 3-vertex path `(a, b, c)` in `G`. -/
def IsP3 {n : Nat} (G : Graph n) (a b c : Fin n) : Prop :=
  a ≠ c ∧ G.adj a b = true ∧ G.adj b c = true

/-- Predicate for `G - {a, b, c}`. -/
def remP3 {n : Nat} (a b c : Fin n) : Fin n → Bool :=
  fun z => (z != a) && (z != b) && (z != c)

theorem remP3_true_iff {n : Nat} {a b c z : Fin n} :
    remP3 a b c z = true ↔ z ≠ a ∧ z ≠ b ∧ z ≠ c := by
  simp [remP3, Bool.and_eq_true, bne_iff_ne, and_assoc]

/-- Connected component of `u` inside `S`. -/
noncomputable def comp {n : Nat} (G : Graph n) (S : Fin n → Bool) (u : Fin n) : Fin n → Bool :=
  fun z => decide (Reachable G S u z)

theorem comp_true_iff {n : Nat} {G : Graph n} {S : Fin n → Bool} {u z : Fin n} :
    comp G S u z = true ↔ Reachable G S u z := by
  simp [comp]

theorem comp_sub {n : Nat} {G : Graph n} {S : Fin n → Bool} {u z : Fin n}
    (h : comp G S u z = true) : S z = true :=
  (comp_true_iff.mp h).target_mem

theorem comp_connected {n : Nat} (G : Graph n) (S : Fin n → Bool) (u : Fin n) :
    IsConnected G (comp G S u) := by
  intro x y hx hy
  have hux : Reachable G S u x := comp_true_iff.mp hx
  have huy : Reachable G S u y := comp_true_iff.mp hy
  have hxy : Reachable G S x y := hux.symm.trans huy
  -- Lift `Reachable G S x y` to `Reachable G (comp G S u) x y`
  have lift : ∀ {a b}, Reachable G S a b → Reachable G S u a → Reachable G (comp G S u) a b := by
    intro a b hab hua
    induction hab with
    | refl _ => exact Reachable.refl (comp_true_iff.mpr hua)
    | step hsa hadj hrest ih =>
      have hub : Reachable G S u _ :=
        hua.trans (Reachable.step hsa hadj (Reachable.refl hrest.source_mem))
      exact Reachable.step (comp_true_iff.mpr hua) hadj (ih hub)
  exact lift hxy hux

/-- Every connected subgraph `C` with at least 3 vertices contains a 3-vertex path `P₃`. -/
theorem exists_p3_in_connected {n : Nat} (G : Graph n) (C : Fin n → Bool) (u : Fin n)
    (hconn : IsConnected G C) (hu : C u = true) (h3 : 3 ≤ countS C) :
    ∃ x y z : Fin n, IsP3 G x y z ∧ C x = true ∧ C y = true ∧ C z = true := by
  -- Find a vertex `w ≠ u` in `C`
  have hlt1 : ([u] : List (Fin n)).length < ((List.finRange n).filter C).length := by
    simp [countS] at h3 ⊢; omega
  obtain ⟨w, hw_mem, hw_not⟩ := pigeonhole_list ((List.finRange n).filter C) [u]
    ((List.nodup_finRange n).filter C) hlt1
  have hcw : C w = true := (List.mem_filter.mp hw_mem).2
  have hwu : w ≠ u := by simpa using hw_not
  -- From `Reachable G C u w`, extract a neighbour `v₁` of `u` in `C`
  have hv1_ex : ∃ v₁ : Fin n, C v₁ = true ∧ G.adj u v₁ = true := by
    cases hconn u w hu hcw with
    | refl _ => exact absurd rfl hwu
    | step _ hadj hrest => exact ⟨_, hrest.source_mem, hadj⟩
  obtain ⟨v₁, hcv1, huv1⟩ := hv1_ex
  have hv1u : v₁ ≠ u := (edge_ne_of_adj G huv1).symm
  -- Either `u` has another neighbour `v₂ ≠ v₁` in `C`, or `v₁` is the unique neighbour of `u` in `C`
  by_cases hu2 : ∃ v₂ : Fin n, C v₂ = true ∧ G.adj u v₂ = true ∧ v₂ ≠ v₁
  · obtain ⟨v₂, hcv2, huv2, hv21⟩ := hu2
    exact ⟨v₁, u, v₂, ⟨hv21.symm, by rw [G.symm]; exact huv1, huv2⟩, hcv1, hu, hcv2⟩
  · -- Pick `z ∈ C \ {u, v₁}`
    have hlt2 : ([u, v₁] : List (Fin n)).length < ((List.finRange n).filter C).length := by
      simp [countS] at h3 ⊢; omega
    obtain ⟨z, hz_mem, hz_not⟩ := pigeonhole_list ((List.finRange n).filter C) [u, v₁]
      ((List.nodup_finRange n).filter C) hlt2
    have hcz : C z = true := (List.mem_filter.mp hz_mem).2
    simp only [List.mem_cons, not_or] at hz_not
    -- `v₁` must have a neighbour `v₂ ≠ u` in `C`, otherwise `{u, v₁}` is closed in `C`
    have hv2_ex : ∃ v₂ : Fin n, C v₂ = true ∧ G.adj v₁ v₂ = true ∧ v₂ ≠ u := by
      apply Classical.byContradiction
      intro hno
      have hclosed : ∀ a b, C a = true → C b = true →
          (a == u || a == v₁) = true → G.adj a b = true → (b == u || b == v₁) = true := by
        intro a b _ hcb ha hab
        simp only [Bool.or_eq_true, beq_iff_eq] at ha ⊢
        rcases ha with rfl | rfl
        · right
          apply Classical.byContradiction
          intro hne
          exact hu2 ⟨b, hcb, hab, hne⟩
        · left
          apply Classical.byContradiction
          intro hne
          exact hno ⟨b, hcb, hab, hne⟩
      have hreach := hconn u z hu hcz
      have hstay := reachable_stays_in_closed G C (fun t => t == u || t == v₁) hclosed hreach (by simp)
      simp only [Bool.or_eq_true, beq_iff_eq] at hstay
      rcases hstay with rfl | rfl
      · exact hz_not.1 rfl
      · exact hz_not.2.1 rfl
    obtain ⟨v₂, hcv2, hv1v2, hv2u⟩ := hv2_ex
    exact ⟨u, v₁, v₂, ⟨hv2u.symm, huv1, hv1v2⟩, hu, hcv1, hcv2⟩

/-- Helper for Case 2 of Lemma 3: if `x` and `y` are adjacent degree-3 vertices inside `C`,
    each adjacent to two of `{a, b, c}`, and `y` is adjacent to `b`, then `G` is not 2-connected. -/
theorem lemma_p3_case2_adj_b {n : Nat} (G : Graph n)
    (h2 : Is2Connected G) (hreg : G.IsRegular 3)
    {a b c u y w : Fin n}
    (hp3 : IsP3 G a b c)
    (hsu : remP3 a b c u = true) (hsy : remP3 a b c y = true)
    (hsw : remP3 a b c w = true)
    (huy : u ≠ y) (hwu : w ≠ u) (hwy : w ≠ y)
    (hadj_uy : G.adj u y = true)
    (hN_u : ∀ t, G.adj u t = true → t = a ∨ t = b ∨ t = c ∨ t = y)
    (hN_y : ∀ t, G.adj y t = true → t = a ∨ t = b ∨ t = c ∨ t = u)
    (hyb : G.adj y b = true) :
    False := by
  obtain ⟨hac, hab, hbc⟩ := hp3
  obtain ⟨hua, hub, huc⟩ := remP3_true_iff.mp hsu
  obtain ⟨hya, hyb_ne, hyc⟩ := remP3_true_iff.mp hsy
  obtain ⟨hwa, hwb, hwc⟩ := remP3_true_iff.mp hsw
  have hba : G.adj b a = true := by rw [G.symm]; exact hab
  have hby : G.adj b y = true := by rw [G.symm]; exact hyb
  have hbu_false : G.adj u b = false := by
    cases h : G.adj u b with
    | false => rfl
    | true =>
      have hbu : G.adj b u = true := by rw [G.symm]; exact h
      exact absurd (not_four_nbrs G hreg hba hbc hby hbu hac hya.symm hua.symm hyc.symm huc.symm huy.symm) id
  -- `u` has degree 3 and its neighbours lie in `{a, c, y}`, so `u` is adjacent to `a` and `c`
  have hu_nbrs_sub : ∀ z ∈ G.nbrs u, z ∈ ([a, c, y] : List (Fin n)) := by
    intro z hz
    have hzu := (mem_nbrs G u z).mp hz
    rcases hN_u z hzu with rfl | rfl | rfl | rfl
    · simp
    · rw [hbu_false] at hzu; cases hzu
    · simp
    · simp
  have hua_adj : G.adj u a = true := by
    have hmem := mem_of_nodup_subset_eq_len (G.nbrs u) [a, c, y] (nodup_nbrs G u) hu_nbrs_sub
      (by show G.deg u = 3; exact hreg u) (y := a) (by simp)
    exact (mem_nbrs G u a).mp hmem
  have huc_adj : G.adj u c = true := by
    have hmem := mem_of_nodup_subset_eq_len (G.nbrs u) [a, c, y] (nodup_nbrs G u) hu_nbrs_sub
      (by show G.deg u = 3; exact hreg u) (y := c) (by simp)
    exact (mem_nbrs G u c).mp hmem
  -- `y` has a third neighbour besides `u` and `b`, which must be `a` or `c`
  obtain ⟨t, hyt, htu, htb⟩ := exists_third_nbr G hreg (x := y) (p := u) (q := b)
  have htac : t = a ∨ t = c := by
    rcases hN_y t hyt with h | h | h | h
    · exact Or.inl h
    · exact absurd h htb
    · exact Or.inr h
    · exact absurd h htu
  -- `b`'s neighbours are `{a, c, y}`
  have hNb : ∀ z, G.adj b z = true → z = a ∨ z = c ∨ z = y :=
    fun z hz => nbr_eq_of_three_nbrs G hreg hba hbc hby hac hya.symm hyc.symm hz
  rcases htac with hta | htc
  · subst t
    -- `y` is adjacent to `a`; then `Q = {a, b, u, y}` is closed in `G - c`
    have hay : G.adj a y = true := by rw [G.symm]; exact hyt
    have hau : G.adj a u = true := by rw [G.symm]; exact hua_adj
    have hNa : ∀ z, G.adj a z = true → z = b ∨ z = u ∨ z = y :=
      fun z hz => nbr_eq_of_three_nbrs G hreg hab hau hay hub.symm hyb_ne.symm huy hz
    have hNy : ∀ z, G.adj y z = true → z = a ∨ z = b ∨ z = u :=
      fun z hz => nbr_eq_of_three_nbrs G hreg hyt hyb (by rw [G.symm]; exact hadj_uy)
        (edge_ne_of_adj G hab) hua.symm hub.symm hz
    let Q : Fin n → Bool := fun z => (z == a) || (z == b) || (z == u) || (z == y)
    have hclosed : ∀ p q, (p != c) = true → (q != c) = true → Q p = true → G.adj p q = true → Q q = true := by
      intro p q _ hqc hQp hpq
      have hqc' : q ≠ c := bne_iff_ne.mp hqc
      simp only [Q, Bool.or_eq_true, beq_iff_eq] at hQp ⊢
      rcases hQp with ((rfl | rfl) | rfl) | rfl
      · rcases hNa q hpq with rfl | rfl | rfl <;> simp
      · rcases hNb q hpq with rfl | rfl | rfl
        · simp
        · exact absurd rfl hqc'
        · simp
      · rcases hN_u q hpq with rfl | rfl | rfl | rfl
        · simp
        · simp
        · exact absurd rfl hqc'
        · simp
      · rcases hNy q hpq with rfl | rfl | rfl <;> simp
    have hreach := h2.2 c u w (bne_iff_ne.mpr huc) (bne_iff_ne.mpr hwc)
    have hQw := reachable_stays_in_closed G (fun z => z != c) Q hclosed hreach (by simp [Q])
    simp only [Q, Bool.or_eq_true, beq_iff_eq] at hQw
    rcases hQw with ((h | h) | h) | h
    · exact hwa h
    · exact hwb h
    · exact hwu h
    · exact hwy h
  · subst t
    -- `y` is adjacent to `c`; then `Q = {b, c, u, y}` is closed in `G - a`
    have hcy : G.adj c y = true := by rw [G.symm]; exact hyt
    have hcu : G.adj c u = true := by rw [G.symm]; exact huc_adj
    have hcb : G.adj c b = true := by rw [G.symm]; exact hbc
    have hNc : ∀ z, G.adj c z = true → z = b ∨ z = u ∨ z = y :=
      fun z hz => nbr_eq_of_three_nbrs G hreg hcb hcu hcy hub.symm hyb_ne.symm huy hz
    have hNy : ∀ z, G.adj y z = true → z = c ∨ z = b ∨ z = u :=
      fun z hz => nbr_eq_of_three_nbrs G hreg hyt hyb (by rw [G.symm]; exact hadj_uy)
        (edge_ne_of_adj G hcb) huc.symm hub.symm hz
    let Q : Fin n → Bool := fun z => (z == b) || (z == c) || (z == u) || (z == y)
    have hclosed : ∀ p q, (p != a) = true → (q != a) = true → Q p = true → G.adj p q = true → Q q = true := by
      intro p q _ hqa hQp hpq
      have hqa' : q ≠ a := bne_iff_ne.mp hqa
      simp only [Q, Bool.or_eq_true, beq_iff_eq] at hQp ⊢
      rcases hQp with ((rfl | rfl) | rfl) | rfl
      · rcases hNb q hpq with rfl | rfl | rfl
        · exact absurd rfl hqa'
        · simp
        · simp
      · rcases hNc q hpq with rfl | rfl | rfl <;> simp
      · rcases hN_u q hpq with rfl | rfl | rfl | rfl
        · exact absurd rfl hqa'
        · simp
        · simp
        · simp
      · rcases hNy q hpq with rfl | rfl | rfl <;> simp
    have hreach := h2.2 a u w (bne_iff_ne.mpr hua) (bne_iff_ne.mpr hwa)
    have hQw := reachable_stays_in_closed G (fun z => z != a) Q hclosed hreach (by simp [Q])
    simp only [Q, Bool.or_eq_true, beq_iff_eq] at hQw
    rcases hQw with ((h | h) | h) | h
    · exact hwb h
    · exact hwc h
    · exact hwu h
    · exact hwy h

/-- Lemma 3 (Non-Separating P₃ Lemma): every 2-connected cubic simple graph contains
    a 3-vertex path `u₂ - v - u₃` whose removal leaves a connected graph. -/
theorem exists_nonsep_P3 {n : Nat} (G : Graph n)
    (h2 : Is2Connected G) (hreg : G.IsRegular 3) :
    ∃ u₂ v u₃ : Fin n, IsP3 G u₂ v u₃ ∧ IsConnected G (remP3 u₂ v u₃) := by
  apply Classical.byContradiction
  intro hno
  have hdisc : ∀ a b c : Fin n, IsP3 G a b c → ¬ IsConnected G (remP3 a b c) :=
    fun a b c hp hconn => hno ⟨a, b, c, hp, hconn⟩
  have hGconn : IsConnected G (fun _ => true) := isConnected_all_of_2connected G h2
  -- Strong induction on `k` bounding `countS (comp G (remP3 a b c) u)`
  have hmain : ∀ k : Nat, ∀ a b c u : Fin n,
      IsP3 G a b c → remP3 a b c u = true → countS (comp G (remP3 a b c) u) ≤ k → False := by
    intro k
    induction k with
    | zero =>
      intro a b c u _ hsu hle
      have hpos := countS_pos_of_true (comp_true_iff.mpr (Reachable.refl (G := G) hsu))
      omega
    | succ k ih =>
      intro a b c u hp3 hsu hle
      let S := remP3 a b c
      let C := comp G S u
      have hcu : C u = true := comp_true_iff.mpr (Reachable.refl hsu)
      -- Existence of `w` in `S \ C`
      have hw_ex : ∃ w : Fin n, S w = true ∧ C w = false := by
        apply Classical.byContradiction
        intro hnow
        apply hdisc a b c hp3
        intro x y hx hy
        have hcx : C x = true := by
          cases hc : C x with
          | true => rfl
          | false => exact absurd ⟨x, hx, hc⟩ hnow
        have hcy : C y = true := by
          cases hc : C y with
          | true => rfl
          | false => exact absurd ⟨y, hy, hc⟩ hnow
        exact (comp_true_iff.mp hcx).symm.trans (comp_true_iff.mp hcy)
      obtain ⟨w, hsw, hcw_false⟩ := hw_ex
      obtain ⟨hac, hab, hbc⟩ := hp3
      have hba : G.adj b a = true := by rw [G.symm]; exact hab
      have hcb : G.adj c b = true := by rw [G.symm]; exact hbc
      have hca_false_C : C a = false := by
        cases h : C a with
        | false => rfl
        | true => have := comp_sub h; simp [S, remP3] at this
      have hcb_false_C : C b = false := by
        cases h : C b with
        | false => rfl
        | true => have := comp_sub h; simp [S, remP3] at this
      have hcc_false_C : C c = false := by
        cases h : C c with
        | false => rfl
        | true => have := comp_sub h; simp [S, remP3] at this
      -- Claim 1: `notC := fun z => !(C z)` is connected
      let notC : Fin n → Bool := fun z => !(C z)
      have hnotC_b : ∀ z : Fin n, notC z = true → Reachable G notC z b := by
        have hstep : ∀ z tgt : Fin n, Reachable G (fun _ => true) z tgt → tgt = b → notC z = true →
            ∃ p : Fin n, (p = a ∨ p = b ∨ p = c) ∧ Reachable G notC z p := by
          intro z tgt hreach
          induction hreach with
          | @refl r _ =>
            intro htgt hnz
            subst r
            exact ⟨b, Or.inr (Or.inl rfl), Reachable.refl hnz⟩
          | @step x y _ _ hadj _ ih_r =>
            intro htgt hnx
            by_cases hxp : x = a ∨ x = b ∨ x = c
            · exact ⟨x, hxp, Reachable.refl hnx⟩
            · have hsx : S x = true := by
                rw [remP3_true_iff]
                exact ⟨fun h => hxp (Or.inl h), fun h => hxp (Or.inr (Or.inl h)),
                       fun h => hxp (Or.inr (Or.inr h))⟩
              have hny : notC y = true := by
                simp only [notC, Bool.not_eq_true'] at hnx ⊢
                cases hcy : C y with
                | false => rfl
                | true =>
                  have hry : Reachable G S u y := comp_true_iff.mp hcy
                  have hrx : Reachable G S u x :=
                    hry.trans (Reachable.step hry.target_mem (by rw [G.symm]; exact hadj) (Reachable.refl hsx))
                  have hcx : C x = true := comp_true_iff.mpr hrx
                  rw [hcx] at hnx; cases hnx
              obtain ⟨p, hp, hryp⟩ := ih_r htgt hny
              exact ⟨p, hp, Reachable.step hnx hadj hryp⟩
        intro z hnz
        obtain ⟨p, hp, hrzp⟩ := hstep z b (hGconn z b rfl rfl) rfl hnz
        have hpb : Reachable G notC p b := by
          rcases hp with rfl | rfl | rfl
          · exact Reachable.step (by simp [notC, hca_false_C]) hab (Reachable.refl (by simp [notC, hcb_false_C]))
          · exact Reachable.refl (by simp [notC, hcb_false_C])
          · exact Reachable.step (by simp [notC, hcc_false_C]) hcb (Reachable.refl (by simp [notC, hcb_false_C]))
        exact hrzp.trans hpb
      have hnotC_conn : IsConnected G notC :=
        fun x y hx hy => (hnotC_b x hx).trans (hnotC_b y hy).symm
      -- Claim 2: `countS C ≤ 2`
      by_cases hC3 : 3 ≤ countS C
      · obtain ⟨x', y', z', hp3', hcx', hcy', hcz'⟩ :=
          exists_p3_in_connected G C u (comp_connected G S u) hcu hC3
        let S' := remP3 x' y' z'
        have hnotC_sub_S' : ∀ t, notC t = true → S' t = true := by
          intro t hnt
          simp only [notC, Bool.not_eq_true'] at hnt
          rw [remP3_true_iff]
          refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
          · subst h; rw [hcx'] at hnt; cases hnt
          · subst h; rw [hcy'] at hnt; cases hnt
          · subst h; rw [hcz'] at hnt; cases hnt
        have hsb' : S' b = true := hnotC_sub_S' b (by simp [notC, hcb_false_C])
        -- Since `S'` is disconnected, some `u'` in `S'` cannot reach `b` in `S'`
        have hu'_ex : ∃ u' : Fin n, S' u' = true ∧ ¬ Reachable G S' u' b := by
          apply Classical.byContradiction
          intro hno'
          apply hdisc x' y' z' hp3'
          intro p q hp hq
          have hpb : Reachable G S' p b :=
            Classical.byContradiction (fun hn => hno' ⟨p, hp, hn⟩)
          have hqb : Reachable G S' q b :=
            Classical.byContradiction (fun hn => hno' ⟨q, hq, hn⟩)
          exact hpb.trans hqb.symm
        obtain ⟨u', hsu', hu'_not_b⟩ := hu'_ex
        let C' := comp G S' u'
        have hC'_sub_C : ∀ t, C' t = true → C t = true := by
          intro t ht
          have hrut : Reachable G S' u' t := comp_true_iff.mp ht
          cases hct : C t with
          | true => rfl
          | false =>
            have hnt : notC t = true := by simp [notC, hct]
            have htb : Reachable G S' t b := (hnotC_b t hnt).mono hnotC_sub_S'
            exact absurd (hrut.trans htb) hu'_not_b
        have hC'_x' : C' x' = false := by
          cases h : C' x' with
          | false => rfl
          | true => have := comp_sub h; simp [S', remP3] at this
        have hltC : countS C' < countS C := countS_lt_of_ssub hC'_sub_C hC'_x' hcx'
        exact ih x' y' z' u' hp3' hsu' (by change countS C' ≤ k; change countS C ≤ k + 1 at hle; omega)
      · -- Now `1 ≤ countS C ≤ 2`
        have hCpos : 0 < countS C := countS_pos_of_true hcu
        by_cases hC1 : countS C = 1
        · -- CASE 1: `|V(C)| = 1`, so `C = {u}`
          have hC_eq_u : ∀ t, C t = true → t = u := by
            intro t ht
            apply Classical.byContradiction
            intro htu
            have hnd : ([u, t] : List (Fin n)).Nodup := by simp [Ne.symm htu]
            have hsub : ∀ z ∈ ([u, t] : List (Fin n)), z ∈ (List.finRange n).filter C := by
              intro z hz
              rw [List.mem_filter]
              refine ⟨List.mem_finRange z, ?_⟩
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hcu
              · have := List.mem_singleton.mp hz; subst this; exact ht
            have hle2 := nodup_length_le_of_subset _ _ hnd hsub
            simp [countS] at hC1; simp at hle2; omega
          -- Every neighbour of `u` lies in `{a, b, c}`
          have hNu_sub : ∀ t ∈ G.nbrs u, t ∈ ([a, b, c] : List (Fin n)) := by
            intro t ht
            have hut : G.adj u t = true := (mem_nbrs G u t).mp ht
            by_cases htp : t = a ∨ t = b ∨ t = c
            · rcases htp with rfl | rfl | rfl <;> simp
            · have hst : S t = true := by
                rw [remP3_true_iff]
                exact ⟨fun h => htp (Or.inl h), fun h => htp (Or.inr (Or.inl h)),
                       fun h => htp (Or.inr (Or.inr h))⟩
              have hct : C t = true := comp_true_iff.mpr (Reachable.step hsu hut (Reachable.refl hst))
              have htu : t = u := hC_eq_u t hct
              subst htu; rw [G.loopless] at hut; cases hut
          have hua_adj : G.adj u a = true :=
            (mem_nbrs G u a).mp (mem_of_nodup_subset_eq_len (G.nbrs u) [a, b, c]
              (nodup_nbrs G u) hNu_sub (by show G.deg u = 3; exact hreg u) (by simp))
          have hub_adj : G.adj u b = true :=
            (mem_nbrs G u b).mp (mem_of_nodup_subset_eq_len (G.nbrs u) [a, b, c]
              (nodup_nbrs G u) hNu_sub (by show G.deg u = 3; exact hreg u) (by simp))
          have huc_adj : G.adj u c = true :=
            (mem_nbrs G u c).mp (mem_of_nodup_subset_eq_len (G.nbrs u) [a, b, c]
              (nodup_nbrs G u) hNu_sub (by show G.deg u = 3; exact hreg u) (by simp))
          have hau_adj : G.adj a u = true := by rw [G.symm]; exact hua_adj
          have hbu_adj : G.adj b u = true := by rw [G.symm]; exact hub_adj
          have hcu_adj : G.adj c u = true := by rw [G.symm]; exact huc_adj
          obtain ⟨hua_ne, hub_ne, huc_ne⟩ := remP3_true_iff.mp hsu
          obtain ⟨hwa_ne, hwb_ne, hwc_ne⟩ := remP3_true_iff.mp hsw
          have hwu_ne : w ≠ u := fun h => by subst h; rw [hcu] at hcw_false; cases hcw_false
          have hNb : ∀ z, G.adj b z = true → z = a ∨ z = c ∨ z = u :=
            fun z hz => nbr_eq_of_three_nbrs G hreg hba hbc hbu_adj hac hua_ne.symm huc_ne.symm hz
          -- `G.adj a c = false` (otherwise `{a, b, c, u}` is a connected component missing `w`)
          have hac_adj_false : G.adj a c = false := by
            cases hac_e : G.adj a c with
            | false => rfl
            | true =>
              have hca_e : G.adj c a = true := by rw [G.symm]; exact hac_e
              have hNa : ∀ z, G.adj a z = true → z = b ∨ z = c ∨ z = u :=
                fun z hz => nbr_eq_of_three_nbrs G hreg hab hac_e hau_adj
                  (edge_ne_of_adj G hbc) hub_ne.symm huc_ne.symm hz
              have hNc : ∀ z, G.adj c z = true → z = a ∨ z = b ∨ z = u :=
                fun z hz => nbr_eq_of_three_nbrs G hreg hca_e hcb hcu_adj
                  (edge_ne_of_adj G hab) hua_ne.symm hub_ne.symm hz
              let Q : Fin n → Bool := fun z => (z == a) || (z == b) || (z == c) || (z == u)
              have hcl : ∀ p q, true = true → true = true → Q p = true → G.adj p q = true → Q q = true := by
                intro p q _ _ hQp hpq
                simp only [Q, Bool.or_eq_true, beq_iff_eq] at hQp ⊢
                rcases hQp with ((hp | hp) | hp) | hp
                · subst p; rcases hNa q hpq with rfl | rfl | rfl <;> simp
                · subst p; rcases hNb q hpq with rfl | rfl | rfl <;> simp
                · subst p; rcases hNc q hpq with rfl | rfl | rfl <;> simp
                · subst p
                  have := hNu_sub q ((mem_nbrs G u q).mpr hpq)
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
                  rcases this with rfl | rfl | rfl <;> simp
              have hQw := reachable_stays_in_closed G (fun _ => true) Q hcl (hGconn b w rfl rfl) (by simp [Q])
              simp only [Q, Bool.or_eq_true, beq_iff_eq] at hQw
              exfalso
              rcases hQw with ((h | h) | h) | h
              · exact hwa_ne h
              · exact hwb_ne h
              · exact hwc_ne h
              · exact hwu_ne h
          -- Let `R z := S z && !(C z)`. Find unique neighbours `a'` of `a` and `c'` of `c` in `R`.
          let R : Fin n → Bool := fun z => S z && !(C z)
          obtain ⟨a', haa', ha'b, ha'u⟩ := exists_third_nbr G hreg (x := a) (p := b) (q := u)
          have ha'a : a' ≠ a := (edge_ne_of_adj G haa').symm
          have ha'c : a' ≠ c := fun h => by subst h; rw [hac_adj_false] at haa'; cases haa'
          have hRa' : R a' = true := by
            have hsa' : S a' = true := remP3_true_iff.mpr ⟨ha'a, ha'b, ha'c⟩
            have hca' : C a' = false := by
              cases h : C a' with
              | false => rfl
              | true => exact absurd (hC_eq_u a' h) ha'u
            simp [R, hsa', hca']
          have hNa : ∀ z, G.adj a z = true → z = b ∨ z = u ∨ z = a' :=
            fun z hz => nbr_eq_of_three_nbrs G hreg hab hau_adj haa' hub_ne.symm ha'b.symm ha'u.symm hz
          obtain ⟨c', hcc', hc'b, hc'u⟩ := exists_third_nbr G hreg (x := c) (p := b) (q := u)
          have hc'c : c' ≠ c := (edge_ne_of_adj G hcc').symm
          have hc'a : c' ≠ a := fun h => by
            subst h; rw [G.symm, hac_adj_false] at hcc'; cases hcc'
          have hRc' : R c' = true := by
            have hsc' : S c' = true := remP3_true_iff.mpr ⟨hc'a, hc'b, hc'c⟩
            have hcc'f : C c' = false := by
              cases h : C c' with
              | false => rfl
              | true => exact absurd (hC_eq_u c' h) hc'u
            simp [R, hsc', hcc'f]
          have hNc : ∀ z, G.adj c z = true → z = b ∨ z = u ∨ z = c' :=
            fun z hz => nbr_eq_of_three_nbrs G hreg hcb hcu_adj hcc' hub_ne.symm hc'b.symm hc'u.symm hz
          -- Helper: if `R t = false`, `t ≠ c`, `R s = true`, `G.adj t s = true`, then `s = a'`
          have hexit_c : ∀ t s, t ≠ c → R t = false → R s = true → G.adj t s = true → s = a' := by
            intro t s htc hRt hRs hts
            have hRs' : S s = true ∧ C s = false := by
              simpa [R, Bool.and_eq_true, Bool.not_eq_true'] using hRs
            obtain ⟨hsa_ne, hsb_ne, hsc_ne⟩ := remP3_true_iff.mp hRs'.1
            have hsu_ne : s ≠ u := fun h => by subst h; rw [hcu] at hRs'; cases hRs'.2
            have ht_in : t = a ∨ t = b ∨ t = u := by
              by_cases hst : S t = true
              · have hct : C t = true := by
                  cases hc : C t with
                  | true => rfl
                  | false => simp [R, hst, hc] at hRt
                exact Or.inr (Or.inr (hC_eq_u t hct))
              · cases hst' : S t with
                | true => exact absurd hst' hst
                | false =>
                  have hnot : ¬ (t ≠ a ∧ t ≠ b ∧ t ≠ c) := by
                    intro h3
                    have htr : S t = true := remP3_true_iff.mpr h3
                    rw [hst'] at htr; cases htr
                  by_cases hta : t = a
                  · exact Or.inl hta
                  · by_cases htb : t = b
                    · exact Or.inr (Or.inl htb)
                    · exact absurd ⟨hta, htb, htc⟩ hnot
            rcases ht_in with ht | ht | ht
            · subst t
              rcases hNa s hts with rfl | rfl | rfl
              · exact absurd rfl hsb_ne
              · exact absurd rfl hsu_ne
              · rfl
            · subst t
              rcases hNb s hts with rfl | rfl | rfl
              · exact absurd rfl hsa_ne
              · exact absurd rfl hsc_ne
              · exact absurd rfl hsu_ne
            · subst t
              have := hNu_sub s ((mem_nbrs G u s).mpr hts)
              simp only [List.mem_cons, List.not_mem_nil, or_false] at this
              rcases this with rfl | rfl | rfl
              · exact absurd rfl hsa_ne
              · exact absurd rfl hsb_ne
              · exact absurd rfl hsc_ne
          -- Prove `Reachable G R a' c'` from `Reachable G (· != c) a' c'`
          have ha'c'_reach : Reachable G R a' c' := by
            have haux : ∀ t tgt, Reachable G (fun z => z != c) t tgt → tgt = c' →
                (R t = true → Reachable G R t c' ∨ Reachable G R a' c') ∧
                (R t = false → Reachable G R a' c') := by
              intro t tgt hreach
              induction hreach with
              | @refl r _ =>
                intro htgt; subst r
                exact ⟨fun _ => Or.inl (Reachable.refl hRc'), fun h => by rw [hRc'] at h; cases h⟩
              | @step p q _ htc hadj hrest ih_r =>
                intro htgt
                have ih' := ih_r htgt
                constructor
                · intro hRp
                  cases hRq : R q with
                  | true =>
                    rcases ih'.1 hRq with hqc' | ha'c'
                    · exact Or.inl (Reachable.step hRp hadj hqc')
                    · exact Or.inr ha'c'
                  | false => exact Or.inr (ih'.2 hRq)
                · intro hRp
                  cases hRq : R q with
                  | false => exact ih'.2 hRq
                  | true =>
                    have hqa' : q = a' := hexit_c p q (bne_iff_ne.mp htc) hRp hRq hadj
                    subst q
                    rcases ih'.1 hRq with h | h <;> exact h
            have h2c := h2.2 c a' c' (bne_iff_ne.mpr ha'c) (bne_iff_ne.mpr hc'c)
            rcases (haux a' c' h2c rfl).1 hRa' with h | h <;> exact h
          -- Every `z ∈ R` reaches `a'` or `c'` in `R`, hence reaches `c'` in `R`
          have hz_to_c' : ∀ z, R z = true → Reachable G R z c' := by
            have hto_bd : ∀ z tgt, Reachable G (fun _ => true) z tgt → tgt = b → R z = true →
                Reachable G R z a' ∨ Reachable G R z c' := by
              intro z tgt hreach
              induction hreach with
              | @refl r _ => intro htgt hRb; subst r; simp [R, S, remP3] at hRb
              | @step p q _ _ hadj _ ih_r =>
                intro htgt hRp
                cases hRq : R q with
                | true =>
                  rcases ih_r htgt hRq with h1 | h2
                  · exact Or.inl (Reachable.step hRp hadj h1)
                  · exact Or.inr (Reachable.step hRp hadj h2)
                | false =>
                  by_cases hqc : q = c
                  · subst q
                    have hpc' : p = c' := by
                      have hRp' : S p = true ∧ C p = false := by
                        simpa [R, Bool.and_eq_true, Bool.not_eq_true'] using hRp
                      obtain ⟨_, hpb_ne, _⟩ := remP3_true_iff.mp hRp'.1
                      have hpu_ne : p ≠ u := fun h => by subst h; rw [hcu] at hRp'; cases hRp'.2
                      rcases hNc p (by rw [G.symm]; exact hadj) with rfl | rfl | rfl
                      · exact absurd rfl hpb_ne
                      · exact absurd rfl hpu_ne
                      · rfl
                    subst p
                    exact Or.inr (Reachable.refl hRc')
                  · have hpa' : p = a' := hexit_c q p hqc hRq hRp (by rw [G.symm]; exact hadj)
                    subst p
                    exact Or.inl (Reachable.refl hRa')
            intro z hRz
            rcases hto_bd z b (hGconn z b rfl rfl) rfl hRz with h1 | h2
            · exact h1.trans ha'c'_reach
            · exact h2
          -- Contradiction: `P' = (u, b, c)` has `remP3 u b c` connected!
          have hp3' : IsP3 G u b c := ⟨huc_ne, hub_adj, hbc⟩
          apply hdisc u b c hp3'
          have hR_sub : ∀ z, R z = true → remP3 u b c z = true := by
            intro z hRz
            have hRz' : S z = true ∧ C z = false := by
              simpa [R, Bool.and_eq_true, Bool.not_eq_true'] using hRz
            obtain ⟨_, hzb, hzc⟩ := remP3_true_iff.mp hRz'.1
            have hzu : z ≠ u := fun h => by subst h; rw [hcu] at hRz'; cases hRz'.2
            exact remP3_true_iff.mpr ⟨hzu, hzb, hzc⟩
          have hto_c'_new : ∀ z, remP3 u b c z = true → Reachable G (remP3 u b c) z c' := by
            intro z hz
            obtain ⟨hzu, hzb, hzc⟩ := remP3_true_iff.mp hz
            by_cases hza : z = a
            · subst hza
              exact Reachable.step hz haa' ((hz_to_c' a' hRa').mono hR_sub)
            · have hsz : S z = true := remP3_true_iff.mpr ⟨hza, hzb, hzc⟩
              have hcz : C z = false := by
                cases hc : C z with
                | false => rfl
                | true => exact absurd (hC_eq_u z hc) hzu
              exact (hz_to_c' z (by simp [R, hsz, hcz])).mono hR_sub
          intro x y hx hy
          exact (hto_c'_new x hx).trans (hto_c'_new y hy).symm
        · -- CASE 2: `|V(C)| = 2`, so `C = {u, y}`
          have hC2 : countS C = 2 := by omega
          have hlt1 : ([u] : List (Fin n)).length < ((List.finRange n).filter C).length := by
            simp [countS] at hC2 ⊢; omega
          obtain ⟨y, hy_mem, hy_not⟩ := pigeonhole_list ((List.finRange n).filter C) [u]
            ((List.nodup_finRange n).filter C) hlt1
          have hcy : C y = true := (List.mem_filter.mp hy_mem).2
          have hyu : y ≠ u := by simpa using hy_not
          have hsy : S y = true := comp_sub hcy
          have hC_eq_uy : ∀ t, C t = true → t = u ∨ t = y := by
            intro t ht
            apply Classical.byContradiction
            intro hnot
            rw [not_or] at hnot
            have hnd : ([u, y, t] : List (Fin n)).Nodup := by
              simp [hyu.symm, Ne.symm hnot.1, Ne.symm hnot.2]
            have hsub : ∀ z ∈ ([u, y, t] : List (Fin n)), z ∈ (List.finRange n).filter C := by
              intro z hz
              rw [List.mem_filter]
              refine ⟨List.mem_finRange z, ?_⟩
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hcu
              · rcases List.mem_cons.mp hz with rfl | hz
                · exact hcy
                · have := List.mem_singleton.mp hz; subst this; exact ht
            have hle3 := nodup_length_le_of_subset _ _ hnd hsub
            simp [countS] at hC2; simp at hle3; omega
          have hadj_uy : G.adj u y = true := by
            cases comp_connected G S u u y hcu hcy with
            | refl _ => exact absurd rfl hyu.symm
            | step _ hadj hrest =>
              rename_i z _
              have hcz : C z = true := hrest.source_mem
              rcases hC_eq_uy z hcz with rfl | rfl
              · rw [G.loopless] at hadj; cases hadj
              · exact hadj
          have hN_u : ∀ t, G.adj u t = true → t = a ∨ t = b ∨ t = c ∨ t = y := by
            intro t hut
            by_cases htp : t = a ∨ t = b ∨ t = c
            · rcases htp with rfl | rfl | rfl <;> simp
            · have hst : S t = true := remP3_true_iff.mpr
                ⟨fun h => htp (Or.inl h), fun h => htp (Or.inr (Or.inl h)), fun h => htp (Or.inr (Or.inr h))⟩
              have hct : C t = true := comp_true_iff.mpr (Reachable.step hsu hut (Reachable.refl hst))
              rcases hC_eq_uy t hct with rfl | rfl
              · rw [G.loopless] at hut; cases hut
              · exact Or.inr (Or.inr (Or.inr rfl))
          have hN_y : ∀ t, G.adj y t = true → t = a ∨ t = b ∨ t = c ∨ t = u := by
            intro t hyt
            by_cases htp : t = a ∨ t = b ∨ t = c
            · rcases htp with rfl | rfl | rfl <;> simp
            · have hst : S t = true := remP3_true_iff.mpr
                ⟨fun h => htp (Or.inl h), fun h => htp (Or.inr (Or.inl h)), fun h => htp (Or.inr (Or.inr h))⟩
              have hct : C t = true := comp_true_iff.mpr
                ((comp_true_iff.mp hcy).trans (Reachable.step hsy hyt (Reachable.refl hst)))
              rcases hC_eq_uy t hct with rfl | rfl
              · exact Or.inr (Or.inr (Or.inr rfl))
              · rw [G.loopless] at hyt; cases hyt
          have hwu : w ≠ u := fun h => by subst h; rw [hcu] at hcw_false; cases hcw_false
          have hwy : w ≠ y := fun h => by subst h; rw [hcy] at hcw_false; cases hcw_false
          cases hyb : G.adj y b with
          | true =>
            exact lemma_p3_case2_adj_b G h2 hreg ⟨hac, hab, hbc⟩ hsu hsy hsw hyu.symm hwu hwy hadj_uy hN_u hN_y hyb
          | false =>
            cases hub : G.adj u b with
            | true =>
              exact lemma_p3_case2_adj_b G h2 hreg ⟨hac, hab, hbc⟩ hsy hsu hsw hyu hwy hwu
                (by rw [G.symm]; exact hadj_uy) hN_y hN_u hub
            | false =>
              -- Neither `u` nor `y` is adjacent to `b`, so both are adjacent to `a` and `c`!
              have hu_sub : ∀ z ∈ G.nbrs u, z ∈ ([a, c, y] : List (Fin n)) := by
                intro z hz
                have hzu := (mem_nbrs G u z).mp hz
                rcases hN_u z hzu with rfl | rfl | rfl | rfl
                · simp
                · rw [hub] at hzu; cases hzu
                · simp
                · simp
              have hy_sub : ∀ z ∈ G.nbrs y, z ∈ ([a, c, u] : List (Fin n)) := by
                intro z hz
                have hzy := (mem_nbrs G y z).mp hz
                rcases hN_y z hzy with rfl | rfl | rfl | rfl
                · simp
                · rw [hyb] at hzy; cases hzy
                · simp
                · simp
              have hua_e : G.adj u a = true := (mem_nbrs G u a).mp
                (mem_of_nodup_subset_eq_len (G.nbrs u) [a, c, y] (nodup_nbrs G u) hu_sub
                  (by show G.deg u = 3; exact hreg u) (by simp))
              have huc_e : G.adj u c = true := (mem_nbrs G u c).mp
                (mem_of_nodup_subset_eq_len (G.nbrs u) [a, c, y] (nodup_nbrs G u) hu_sub
                  (by show G.deg u = 3; exact hreg u) (by simp))
              have hya_e : G.adj y a = true := (mem_nbrs G y a).mp
                (mem_of_nodup_subset_eq_len (G.nbrs y) [a, c, u] (nodup_nbrs G y) hy_sub
                  (by show G.deg y = 3; exact hreg y) (by simp))
              have hyc_e : G.adj y c = true := (mem_nbrs G y c).mp
                (mem_of_nodup_subset_eq_len (G.nbrs y) [a, c, u] (nodup_nbrs G y) hy_sub
                  (by show G.deg y = 3; exact hreg y) (by simp))
              obtain ⟨hua_ne, hub_ne, huc_ne⟩ := remP3_true_iff.mp hsu
              obtain ⟨hya_ne, hyb_ne, hyc_ne⟩ := remP3_true_iff.mp hsy
              obtain ⟨hwa_ne, hwb_ne, hwc_ne⟩ := remP3_true_iff.mp hsw
              have hNa : ∀ z, G.adj a z = true → z = b ∨ z = u ∨ z = y :=
                fun z hz => nbr_eq_of_three_nbrs G hreg hab (by rw [G.symm]; exact hua_e)
                  (by rw [G.symm]; exact hya_e) hub_ne.symm hyb_ne.symm hyu.symm hz
              have hNc : ∀ z, G.adj c z = true → z = b ∨ z = u ∨ z = y :=
                fun z hz => nbr_eq_of_three_nbrs G hreg hcb (by rw [G.symm]; exact huc_e)
                  (by rw [G.symm]; exact hyc_e) hub_ne.symm hyb_ne.symm hyu.symm hz
              let Q : Fin n → Bool := fun z => (z == a) || (z == c) || (z == u) || (z == y)
              have hcl : ∀ p q, (p != b) = true → (q != b) = true → Q p = true → G.adj p q = true → Q q = true := by
                intro p q _ hqb hQp hpq
                have hqb' : q ≠ b := bne_iff_ne.mp hqb
                simp only [Q, Bool.or_eq_true, beq_iff_eq] at hQp ⊢
                rcases hQp with ((rfl | rfl) | rfl) | rfl
                · rcases hNa q hpq with rfl | rfl | rfl
                  · exact absurd rfl hqb'
                  · simp
                  · simp
                · rcases hNc q hpq with rfl | rfl | rfl
                  · exact absurd rfl hqb'
                  · simp
                  · simp
                · rcases hN_u q hpq with rfl | rfl | rfl | rfl
                  · simp
                  · exact absurd rfl hqb'
                  · simp
                  · simp
                · rcases hN_y q hpq with rfl | rfl | rfl | rfl
                  · simp
                  · exact absurd rfl hqb'
                  · simp
                  · simp
              have hQw := reachable_stays_in_closed G (fun z => z != b) Q hcl
                (h2.2 b u w (bne_iff_ne.mpr hub_ne) (bne_iff_ne.mpr hwb_ne)) (by simp [Q])
              simp only [Q, Bool.or_eq_true, beq_iff_eq] at hQw
              rcases hQw with ((h | h) | h) | h
              · exact hwa_ne h
              · exact hwc_ne h
              · exact hwu h
              · exact hwy h
  -- Finally, exhibit any 3-vertex path `(u₂, v, u₃)` and any 4th vertex `u₁` (from `G.deg v = 3`)
  have hn : 3 ≤ n := h2.1
  let v0 : Fin n := ⟨0, by omega⟩
  have hdeg0 : (G.nbrs v0).length = 3 := hreg v0
  match hnb : G.nbrs v0 with
  | [a0, b0, c0] =>
    have hnd0 : ([a0, b0, c0] : List (Fin n)).Nodup := by rw [← hnb]; exact nodup_nbrs G v0
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd0
    have ha0 : G.adj v0 a0 = true := (mem_nbrs G v0 a0).mp (by rw [hnb]; simp)
    have hb0 : G.adj v0 b0 = true := (mem_nbrs G v0 b0).mp (by rw [hnb]; simp)
    have hc0 : G.adj v0 c0 = true := (mem_nbrs G v0 c0).mp (by rw [hnb]; simp)
    have hp3_0 : IsP3 G a0 v0 b0 := ⟨hnd0.1.1, by rw [G.symm]; exact ha0, hb0⟩
    have hsc0 : remP3 a0 v0 b0 c0 = true :=
      remP3_true_iff.mpr ⟨Ne.symm hnd0.1.2, (edge_ne_of_adj G hc0).symm, Ne.symm hnd0.2.1⟩
    exact hmain n a0 v0 b0 c0 hp3_0 hsc0 (by
      have hlen := List.length_filter_le (comp G (remP3 a0 v0 b0) c0) (List.finRange n)
      rw [List.length_finRange] at hlen
      exact hlen)
  | [] => rw [hnb] at hdeg0; simp at hdeg0
  | [_] => rw [hnb] at hdeg0; simp at hdeg0
  | [_, _] => rw [hnb] at hdeg0; simp at hdeg0
  | _ :: _ :: _ :: _ :: _ => rw [hnb] at hdeg0; simp at hdeg0

/-- Proof of Theorem A for `d = 3` (works for any proper edge colouring `w`). -/
theorem theorem_regular_3 {n : Nat} {C : Type} [DecidableEq C]
    (G : Graph n) (w : Edge n → C)
    (h2 : Is2Connected G) (hreg : G.IsRegular 3)
    (hprop : IsProperEdgeColoring G w) :
    SequentiallyOrderable G w := by
  obtain ⟨u₂, v, u₃, ⟨hu23, hu2v, hvu3⟩, hKconn⟩ := exists_nonsep_P3 G h2 hreg
  have hvu2 : G.adj v u₂ = true := by rw [G.symm]; exact hu2v
  have hu2v_ne : u₂ ≠ v := edge_ne_of_adj G hu2v
  have hu3v_ne : u₃ ≠ v := (edge_ne_of_adj G hvu3).symm
  -- Find the third neighbour `u₁` of `v`
  obtain ⟨u₁, hvu1, hu12, hu13⟩ := exists_third_nbr G hreg (x := v) (p := u₂) (q := u₃)
  have hu1v_ne : u₁ ≠ v := (edge_ne_of_adj G hvu1).symm
  have hNv : ∀ z, G.adj v z = true → z = u₁ ∨ z = u₂ ∨ z = u₃ :=
    fun z hz => nbr_eq_of_three_nbrs G hreg hvu1 hvu2 hvu3 hu12 hu13 hu23 hz
  -- Elimination order of `K = G - {u₂, v, u₃}` rooted at `u₁`
  have hKu1 : remP3 u₂ v u₃ u₁ = true := remP3_true_iff.mpr ⟨hu12, hu1v_ne, hu13⟩
  obtain ⟨xs, hxs_nd, hxs_cov, hxs_ln⟩ :=
    exists_elimination_order G (remP3 u₂ v u₃) u₁ hKconn hKu1
  -- Lift `HasLaterNbr` from `remP3 u₂ v u₃` to `fun z => z != v`
  have lift_ln : ∀ l : List (Fin n),
      HasLaterNbr G (remP3 u₂ v u₃) l → HasLaterNbr G (fun z => z != v) l := by
    intro l
    induction l with
    | nil => intro _; trivial
    | cons a rest ih =>
      cases rest with
      | nil => intro _; trivial
      | cons b rest' =>
        rintro ⟨⟨z, hz, hsz, haz⟩, htail⟩
        exact ⟨⟨z, hz, bne_iff_ne.mpr (remP3_true_iff.mp hsz).2.1, haz⟩, ih htail⟩
  have hxs_ln_H : HasLaterNbr G (fun z => z != v) (xs ++ [u₁]) := lift_ln (xs ++ [u₁]) hxs_ln
  -- Initial edges `S2 = E_H(u₂) ∪ E_H(u₃)` ordered with non-`c₁` edges before `c₁` edges
  let e_vu1 := mkEdge v u₁ (edge_ne_of_adj G hvu1)
  let e_vu2 := mkEdge v u₂ (edge_ne_of_adj G hvu2)
  let e_vu3 := mkEdge v u₃ (edge_ne_of_adj G hvu3)
  let c₁ := w e_vu1
  let c₂ := w e_vu2
  let c₃ := w e_vu3
  have hc12 : c₁ ≠ c₂ := hprop e_vu1 e_vu2
    (by rw [mkEdge_isEdge]; exact hvu1) (by rw [mkEdge_isEdge]; exact hvu2)
    (fun h => hu12 (mkEdge_inj_left _ _ h))
    ⟨v, (mkEdge_incident v u₁ v _).mpr (Or.inl rfl), (mkEdge_incident v u₂ v _).mpr (Or.inl rfl)⟩
  have hc13 : c₁ ≠ c₃ := hprop e_vu1 e_vu3
    (by rw [mkEdge_isEdge]; exact hvu1) (by rw [mkEdge_isEdge]; exact hvu3)
    (fun h => hu13 (mkEdge_inj_left _ _ h))
    ⟨v, (mkEdge_incident v u₁ v _).mpr (Or.inl rfl), (mkEdge_incident v u₃ v _).mpr (Or.inl rfl)⟩
  have hc23 : c₂ ≠ c₃ := hprop e_vu2 e_vu3
    (by rw [mkEdge_isEdge]; exact hvu2) (by rw [mkEdge_isEdge]; exact hvu3)
    (fun h => hu23 (mkEdge_inj_left _ _ h))
    ⟨v, (mkEdge_incident v u₂ v _).mpr (Or.inl rfl), (mkEdge_incident v u₃ v _).mpr (Or.inl rfl)⟩
  -- Build a nodup list `S2` of all edges in `E_H(u₂) ∪ E_H(u₃)`
  let E2 := (G.incEdges u₂).filter (fun e => e.incident v == false)
  let E3 := (G.incEdges u₃).filter (fun e => e.incident v == false && !(e ∈ E2))
  let S2 := E2 ++ E3
  have hS2_nd : S2.Nodup := by
    rw [nodup_append_iff]
    refine ⟨(nodup_incEdges G u₂).filter _, (nodup_incEdges G u₃).filter _, fun e he2 he3 => ?_⟩
    have hcond := (List.mem_filter.mp he3).2
    simp [he2] at hcond
  have hS2_mem : ∀ e : Edge n, e ∈ S2 ↔
      e.isEdge G = true ∧ e.incident v = false ∧ (e.incident u₂ = true ∨ e.incident u₃ = true) := by
    intro e
    simp only [S2, List.mem_append, E2, E3, List.mem_filter, mem_incEdges,
      Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3, _⟩)
      · exact ⟨h1, h3, Or.inl h2⟩
      · exact ⟨h1, h3, Or.inr h2⟩
    · rintro ⟨h1, h2, h3 | h3⟩
      · left; exact ⟨⟨h1, h3⟩, h2⟩
      · by_cases he2 : e ∈ E2
        · left
          simpa only [E2, List.mem_filter, mem_incEdges, beq_iff_eq] using he2
        · right; exact ⟨⟨h1, h3⟩, h2, by simpa only [E2, List.mem_filter, mem_incEdges, beq_iff_eq] using he2⟩
  let L2 := S2.filter (fun e => w e != c₁) ++ S2.filter (fun e => w e == c₁)
  have hL2_nd : L2.Nodup := by
    rw [nodup_append_iff]
    refine ⟨hS2_nd.filter _, hS2_nd.filter _, fun e h1 h2 => ?_⟩
    have hb1 : w e ≠ c₁ := bne_iff_ne.mp (List.mem_filter.mp h1).2
    have hb2 : w e = c₁ := beq_iff_eq.mp (List.mem_filter.mp h2).2
    exact hb1 hb2
  have hL2_mem : ∀ e : Edge n, e ∈ L2 ↔
      e.isEdge G = true ∧ e.incident v = false ∧ ∃ y ∈ ([u₂, u₃] : List (Fin n)), e.incident y = true := by
    intro e
    simp only [L2, List.mem_append, List.mem_filter, bne_iff_ne, beq_iff_eq,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩)
      all_goals
        obtain ⟨h1, h2, h3 | h3⟩ := (hS2_mem e).mp he
        · exact ⟨h1, h2, u₂, Or.inl rfl, h3⟩
        · exact ⟨h1, h2, u₃, Or.inr rfl, h3⟩
    · rintro ⟨h1, h2, y, hy2 | hy3, h3⟩
      · subst y
        have hS : e ∈ S2 := (hS2_mem e).mpr ⟨h1, h2, Or.inl h3⟩
        by_cases hw : w e = c₁
        · right; exact ⟨hS, hw⟩
        · left; exact ⟨hS, hw⟩
      · subst y
        have hS : e ∈ S2 := (hS2_mem e).mpr ⟨h1, h2, Or.inr h3⟩
        by_cases hw : w e = c₁
        · right; exact ⟨hS, hw⟩
        · left; exact ⟨hS, hw⟩
  -- Key property 1: `prospSeq G w v u₁ L2 u₂` and `prospSeq G w v u₁ L2 u₃` do not start with `c₁`
  have hhead_ne_c1 : ∀ u' : Fin n, (u' = u₂ ∨ u' = u₃) →
      G.adj v u' = true → u' ≠ u₁ →
      ∀ s : List C, prospSeq G w v u₁ L2 u' ≠ c₁ :: s := by
    intro u' hu'_or hvu' hu'1 s
    have hfilt : L2.filter (fun e => e.incident u') =
        (S2.filter (fun e => w e != c₁)).filter (fun e => e.incident u') ++
        (S2.filter (fun e => w e == c₁)).filter (fun e => e.incident u') :=
      List.filter_append ..
    -- `u'` has 2 neighbours in `H = G - v`, giving 2 distinct edges in `L2.filter (·.incident u')`
    obtain ⟨z₁, hz1_adj, hz1v, _⟩ := exists_third_nbr G hreg (x := u') (p := v) (q := v)
    obtain ⟨z₂, hz2_adj, hz2v, hz21⟩ := exists_third_nbr G hreg (x := u') (p := v) (q := z₁)
    let e₁ := mkEdge u' z₁ (edge_ne_of_adj G hz1_adj)
    let e₂ := mkEdge u' z₂ (edge_ne_of_adj G hz2_adj)
    have he12 : e₁ ≠ e₂ := fun h => hz21.symm (mkEdge_inj_left _ _ h)
    have he1_S2 : e₁ ∈ S2 := by
      rw [hS2_mem]
      refine ⟨by rw [mkEdge_isEdge]; exact hz1_adj, ?_, ?_⟩
      · cases h : e₁.incident v with
        | false => rfl
        | true =>
          dsimp only [e₁] at h; rw [mkEdge_incident] at h
          rcases h with rfl | rfl
          · exact absurd rfl (edge_ne_of_adj G hvu')
          · exact absurd rfl hz1v.symm
      · rcases hu'_or with hu'2 | hu'3
        · rw [← hu'2]; exact Or.inl ((mkEdge_incident u' z₁ u' _).mpr (Or.inl rfl))
        · rw [← hu'3]; exact Or.inr ((mkEdge_incident u' z₁ u' _).mpr (Or.inl rfl))
    have he2_S2 : e₂ ∈ S2 := by
      rw [hS2_mem]
      refine ⟨by rw [mkEdge_isEdge]; exact hz2_adj, ?_, ?_⟩
      · cases h : e₂.incident v with
        | false => rfl
        | true =>
          dsimp only [e₂] at h; rw [mkEdge_incident] at h
          rcases h with rfl | rfl
          · exact absurd rfl (edge_ne_of_adj G hvu')
          · exact absurd rfl hz2v.symm
      · rcases hu'_or with hu'2 | hu'3
        · rw [← hu'2]; exact Or.inl ((mkEdge_incident u' z₂ u' _).mpr (Or.inl rfl))
        · rw [← hu'3]; exact Or.inr ((mkEdge_incident u' z₂ u' _).mpr (Or.inl rfl))
    -- At least one of `e₁, e₂` has colour `≠ c₁` by properness
    have hex_nonc1 : ∃ e ∈ (S2.filter (fun e => w e != c₁)).filter (fun e => e.incident u'), True := by
      by_cases hw1 : w e₁ = c₁
      · have hw2 : w e₂ ≠ c₁ := by
          intro hw2
          exact hprop e₁ e₂ (by rw [mkEdge_isEdge]; exact hz1_adj) (by rw [mkEdge_isEdge]; exact hz2_adj)
            he12 ⟨u', (mkEdge_incident u' z₁ u' _).mpr (Or.inl rfl),
                      (mkEdge_incident u' z₂ u' _).mpr (Or.inl rfl)⟩ (hw1.trans hw2.symm)
        exact ⟨e₂, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨he2_S2, bne_iff_ne.mpr hw2⟩,
                    (mkEdge_incident u' z₂ u' _).mpr (Or.inl rfl)⟩, trivial⟩
      · exact ⟨e₁, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨he1_S2, bne_iff_ne.mpr hw1⟩,
                  (mkEdge_incident u' z₁ u' _).mpr (Or.inl rfl)⟩, trivial⟩
    obtain ⟨e_wit, he_wit, _⟩ := hex_nonc1
    -- Hence the first list in `hfilt` is nonempty, so its head has colour `≠ c₁`
    cases hne : (S2.filter (fun e => w e != c₁)).filter (fun e => e.incident u') with
    | nil => rw [hne] at he_wit; cases he_wit
    | cons e_hd e_tl =>
      have hhd_mem : e_hd ∈ S2.filter (fun e => w e != c₁) := by
        have : e_hd ∈ (S2.filter (fun e => w e != c₁)).filter (fun e => e.incident u') := by
          rw [hne]; exact List.mem_cons_self ..
        exact (List.mem_filter.mp this).1
      have hhd_ne : w e_hd ≠ c₁ := bne_iff_ne.mp (List.mem_filter.mp hhd_mem).2
      unfold prospSeq vertexSeq
      rw [dite_eq_left ⟨hvu', hu'1⟩, hfilt, hne]
      simp only [List.cons_append, List.map_cons, ne_eq, List.cons.injEq, not_and]
      intro hEq
      exact absurd hEq hhd_ne
  -- Key property 2: `prospSeq G w v u₁ L2 u₂ ≠ prospSeq G w v u₁ L2 u₃` (last entries `c₂ ≠ c₃`)
  have hu2_ne_u3 : prospSeq G w v u₁ L2 u₂ ≠ prospSeq G w v u₁ L2 u₃ := by
    unfold prospSeq
    rw [dite_eq_left ⟨hvu2, hu12.symm⟩, dite_eq_left ⟨hvu3, hu13.symm⟩]
    intro hEq
    have hlast := (List.append_inj_right' hEq rfl)
    simp only [List.cons.injEq] at hlast
    exact hc23 hlast.1
  -- Apply Lemma 2 (`greedy_extension`) with `done = [u₂, u₃]`
  have hnd_all : (([u₂, u₃] : List (Fin n)) ++ xs ++ [u₁]).Nodup := by
    rw [List.append_assoc, nodup_append_iff]
    refine ⟨by simp [hu23], hxs_nd, fun z hz hzx => ?_⟩
    have hkz : remP3 u₂ v u₃ z = true := (hxs_cov z).mp hzx
    obtain ⟨hzu2, _, hzu3⟩ := remP3_true_iff.mp hkz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h2 | h3
    · exact hzu2 h2
    · exact hzu3 h3
  have hcov_all : ∀ z : Fin n, z ∈ ([u₂, u₃] : List (Fin n)) ++ xs ++ [u₁] ↔ z ≠ v := by
    intro z
    rw [List.append_assoc, List.mem_append, hxs_cov z, remP3_true_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ((rfl | rfl) | ⟨_, hzv, _⟩)
      · exact hu2v_ne
      · exact hu3v_ne
      · exact hzv
    · intro hzv
      by_cases h2z : z = u₂
      · exact Or.inl (Or.inl h2z)
      · by_cases h3z : z = u₃
        · exact Or.inl (Or.inr h3z)
        · exact Or.inr ⟨h2z, hzv, h3z⟩
  have hdist_init : ∀ a ∈ ([u₂, u₃] : List (Fin n)), ∀ b ∈ ([u₂, u₃] : List (Fin n)),
      G.adj a b = true → prospSeq G w v u₁ L2 a ≠ prospSeq G w v u₁ L2 b := by
    intro a ha b hb hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with ha2 | ha3 <;> rcases hb with hb2 | hb3
    · subst a; subst b; rw [G.loopless] at hab; cases hab
    · subst a; subst b; exact hu2_ne_u3
    · subst a; subst b; exact hu2_ne_u3.symm
    · subst a; subst b; rw [G.loopless] at hab; cases hab
  obtain ⟨L₀, hL₀_nd, hL₀_mem, hL₀_pres, hL₀_dist⟩ :=
    greedy_extension G w hprop v u₁ hvu1 xs [u₂, u₃] L2
      hnd_all hcov_all hxs_ln_H hL2_nd hL2_mem hdist_init
  -- Choose `B_ord` to be `[e_vu2, e_vu3]` or `[e_vu3, e_vu2]` avoiding `prospSeq ... u₁`
  have he23_ne : e_vu2 ≠ e_vu3 := fun h => hu23 (mkEdge_inj_left _ _ h)
  have hcand_ne : ([c₁, c₂, c₃] : List C) ≠ [c₁, c₃, c₂] := by
    intro hEq
    simp only [List.cons.injEq] at hEq
    exact hc23 hEq.2.1
  let B_ord : List (Edge n) :=
    if prospSeq G w v u₁ L₀ u₁ = [c₁, c₂, c₃] then [e_vu3, e_vu2] else [e_vu2, e_vu3]
  have hB_nd : B_ord.Nodup := by
    dsimp only [B_ord]
    split
    · simp [he23_ne.symm]
    · simp [he23_ne]
  have hB_mem : ∀ e : Edge n, e ∈ B_ord ↔
      e.isEdge G = true ∧ e.incident v = true ∧ e ≠ e_vu1 := by
    intro e
    have hB_or : e ∈ B_ord ↔ e = e_vu2 ∨ e = e_vu3 := by
      dsimp only [B_ord]
      split <;> simp [or_comm]
    rw [hB_or]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨by rw [mkEdge_isEdge]; exact hvu2,
               (mkEdge_incident v u₂ v _).mpr (Or.inl rfl),
               fun h => hu12.symm (mkEdge_inj_left _ _ h)⟩
      · exact ⟨by rw [mkEdge_isEdge]; exact hvu3,
               (mkEdge_incident v u₃ v _).mpr (Or.inl rfl),
               fun h => hu13.symm (mkEdge_inj_left _ _ h)⟩
    · rintro ⟨he, hinc, hne⟩
      have he_mem : e ∈ G.incEdges v := (mem_incEdges G v e).mpr ⟨he, hinc⟩
      unfold Graph.incEdges at he_mem
      rw [List.mem_map] at he_mem
      obtain ⟨⟨u, hu⟩, _, rfl⟩ := he_mem
      rcases hNv u ((mem_nbrs G v u).mp hu) with rfl | rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl rfl
      · exact Or.inr rfl
  obtain ⟨hord, hx_eq, hv_eq⟩ :=
    final_block_invariance G w v u₁ hvu1 L₀ B_ord hL₀_nd hL₀_mem hB_nd hB_mem
  have hv_ne_nbr : ∀ u' : Fin n, G.adj v u' = true →
      vertexSeq w (L₀ ++ B_ord) v ≠ vertexSeq w (L₀ ++ B_ord) u' := by
    intro u' hvu'
    have hu'v : u' ≠ v := (edge_ne_of_adj G hvu').symm
    rw [hv_eq, hx_eq u' hu'v]
    rcases hNv u' hvu' with hu'1 | hu'2 | hu'3
    · subst u'
      dsimp only [B_ord]
      split
      · rename_i hEq
        rw [hEq]
        exact hcand_ne.symm
      · rename_i hNe
        intro hEq
        exact hNe hEq.symm
    · subst u'
      rw [hL₀_pres u₂ (by simp)]
      exact (hhead_ne_c1 u₂ (Or.inl rfl) hvu2 hu12.symm (B_ord.map w)).symm
    · subst u'
      rw [hL₀_pres u₃ (by simp)]
      exact (hhead_ne_c1 u₃ (Or.inr rfl) hvu3 hu13.symm (B_ord.map w)).symm
  refine ⟨L₀ ++ B_ord, hord, ?_⟩
  intro a b hab
  by_cases hav : a = v
  · subst a; exact hv_ne_nbr b hab
  · by_cases hbv : b = v
    · subst b; exact (hv_ne_nbr a (by rw [G.symm]; exact hab)).symm
    · rw [hx_eq a hav, hx_eq b hbv]
      exact hL₀_dist a b hav hbv hab

end Cubic

/-! ## Section 6: Unified Main Theorem (Theorem A) -/

/-- **Main Theorem (Resolving Conjecture 10 of Gorzkowska & Kwaśny, 2026):**
    For every integer `d ≥ 3`, every proper edge colouring of a 2-connected
    `d`-regular finite simple graph is sequentially orderable. -/
theorem theorem_regular {n d : Nat} {C : Type} [DecidableEq C]
    (G : Graph n) (w : Edge n → C)
    (hd : 3 ≤ d) (h2 : Is2Connected G) (hreg : G.IsRegular d)
    (hprop : IsProperEdgeColoring G w) :
    SequentiallyOrderable G w := by
  by_cases hd3 : d = 3
  · subst hd3
    exact theorem_regular_3 G w h2 hreg hprop
  · exact theorem_regular_ge_4 G w (by omega) h2 hreg hprop

#print axioms theorem_regular

end SeqOrderable
