import Mathlib
open Finset

/-!
# Conjecture OEIS A401714 ≤ A401715 — squelette complet de la preuve
Preuve complète, sans `sorry`. Claude & ChatGPT, novembre 2026.
-/

namespace A401714


def usigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => Nat.Coprime d (n / d)), d
def ssq (n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => Squarefree d), d


/-- n est le produit des p^(v_p n). -/
lemma n_eq_prod (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  rw [← Nat.prod_factorization_eq_prod_primeFactors]
  exact Nat.prod_factorization_pow_eq_self hn

/-- Les facteurs premiers de ∏_{p∈t} p^(v_p n) sont exactement t. -/
lemma primeFactors_prod_pow (n : ℕ) (t : Finset ℕ) (ht : t ⊆ n.primeFactors) :
    (∏ p ∈ t, p ^ n.factorization p).primeFactors = t := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : s ⊆ n.primeFactors := (Finset.subset_insert _ _).trans ht
    have haP : a ∈ n.primeFactors := ht (Finset.mem_insert_self _ _)
    have hpa : a.Prime := Nat.prime_of_mem_primeFactors haP
    have hea : n.factorization a ≠ 0 :=
      Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization])
    have h1 : a ^ n.factorization a ≠ 0 := pow_ne_zero _ hpa.ne_zero
    have h2 : ∏ p ∈ s, p ^ n.factorization p ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp =>
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hs hp)).ne_zero
    rw [Finset.prod_insert ha, Nat.primeFactors_mul h1 h2, Nat.primeFactors_pow _ hea,
      hpa.primeFactors, ih hs]
    rfl

/-- Deux produits de puissances premières sur des ensembles disjoints sont premiers entre eux. -/
lemma coprime_prod_pow (n : ℕ) (t u : Finset ℕ) (ht : t ⊆ n.primeFactors)
    (hu : u ⊆ n.primeFactors) (hd : Disjoint t u) :
    Nat.Coprime (∏ p ∈ t, p ^ n.factorization p) (∏ p ∈ u, p ^ n.factorization p) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro r hr
  have hpP := Nat.prime_of_mem_primeFactors (ht hp)
  have hrP := Nat.prime_of_mem_primeFactors (hu hr)
  have hne : p ≠ r := fun h => Finset.disjoint_left.mp hd hp (h ▸ hr)
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hpP hrP).mpr hne)

/-- **A1.** ∏ (1 + p^e) ≤ usigma n. -/
lemma usigma_ge (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) ≤ usigma n := by
  classical
  set S := n.primeFactors with hS
  let g : Finset ℕ → ℕ := fun t => ∏ p ∈ t, p ^ n.factorization p
  rw [Finset.prod_one_add]
  have hinj : Set.InjOn g ↑(S.powerset) := by
    intro t ht u hu h
    have ht' : t ⊆ S := Finset.mem_powerset.mp ht
    have hu' : u ⊆ S := Finset.mem_powerset.mp hu
    have := congrArg Nat.primeFactors h
    simp only [g] at this
    rwa [primeFactors_prod_pow n t ht', primeFactors_prod_pow n u hu'] at this
  rw [← Finset.sum_image (f := fun d => d) hinj]
  apply Finset.sum_le_sum_of_subset
  intro d hd
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
  have ht' : t ⊆ S := Finset.mem_powerset.mp ht
  have hsplit : g (S \ t) * g t = n := by
    simp only [g]
    rw [Finset.prod_sdiff ht', n_eq_prod n hn]
  have hgt : g t ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hsplit; exact hn hsplit.symm
  have hdiv : n / g t = g (S \ t) := by
    rw [← hsplit, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hgt)]
  rw [Finset.mem_filter, Nat.mem_divisors]
  refine ⟨⟨⟨g (S \ t), by rw [mul_comm]; exact hsplit.symm⟩, hn⟩, ?_⟩
  rw [hdiv]
  exact coprime_prod_pow n t (S \ t) ht' Finset.sdiff_subset Finset.disjoint_sdiff

/-- **A2.** ∏ (1 + p) ≤ ssq n. -/
lemma ssq_ge (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, (1 + p) ≤ ssq n := by
  classical
  set S := n.primeFactors with hS
  rw [Finset.prod_one_add]
  have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) ↑(S.powerset) := by
    intro t ht u hu h
    have ht' : t ⊆ S := Finset.mem_powerset.mp ht
    have hu' : u ⊆ S := Finset.mem_powerset.mp hu
    have := congrArg Nat.primeFactors h
    simp only at this
    rwa [Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (ht' hp)),
      Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hu' hp))] at this
  rw [← Finset.sum_image (f := fun d => d) hinj]
  apply Finset.sum_le_sum_of_subset
  intro d hd
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
  have ht' : t ⊆ S := Finset.mem_powerset.mp ht
  have hprime : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (ht' hp)
  rw [Finset.mem_filter, Nat.mem_divisors]
  refine ⟨⟨?_, hn⟩, ?_⟩
  · exact Finset.prod_primes_dvd n (fun p hp => (hprime p hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors (ht' hp))
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp r hr hne
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hprime p hp) (hprime r hr)).mpr hne)
    · intro p hp
      exact (hprime p hp).prime.squarefree

/-- Les deux minorations ensemble. -/
lemma somme_ge (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) + ∏ p ∈ n.primeFactors, (1 + p)
      ≤ usigma n + ssq n :=
  Nat.add_le_add (usigma_ge n hn) (ssq_ge n hn)


/-- Radical : produit des premiers distincts. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- Les premiers strictement inférieurs à q. -/
def Pq (q : ℕ) : Finset ℕ := (Finset.range q).filter Nat.Prime

/-- N(q) = ∏_{p<q} (1 + 1/p). -/
noncomputable def Nq (q : ℕ) : ℚ := ∏ p ∈ Pq q, (1 + 1 / (p : ℚ))



/-- Monotonie des produits (dans ℚ) quand on agrandit l'ensemble, facteurs ≥ 1. -/
lemma prodQ_mono {s t : Finset ℕ} (h : s ⊆ t) {f : ℕ → ℚ} (hf : ∀ i ∈ t, 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical
  rw [← Finset.prod_sdiff h]
  have h1 : 1 ≤ ∏ i ∈ t \ s, f i := one_le_prod₀ fun i hi => hf i (Finset.mem_sdiff.mp hi).1
  have h0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => le_trans zero_le_one (hf i (h hi))
  exact le_mul_of_one_le_left h0 h1

/-! ## Étape B : n / rad n = ∏ p^(e-1) -/
lemma div_rad (n : ℕ) (hn : n ≠ 0) :
    n / rad n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) := by
  have hsplit : (∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1)) * rad n = n := by
    rw [rad, ← Finset.prod_mul_distrib]
    conv_rhs => rw [← n_eq_prod n hn]
    apply Finset.prod_congr rfl
    intro p hp
    have he : 1 ≤ n.factorization p :=
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization]))
    rw [← pow_succ, Nat.sub_add_cancel he]
  have hrad : 0 < rad n :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  exact Nat.div_eq_of_eq_mul_left hrad hsplit.symm


/-! ## Étape 1 : petits q (q ≤ 73), vérification finie -/



/-- Valuation p-adique calculable (avec « carburant » k). -/
def vp (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, a => if a ≠ 0 ∧ p ∣ a then vp p k (a / p) + 1 else 0

lemma vp_eq (p : ℕ) (hp : p.Prime) : ∀ k a, a ≤ k → vp p k a = a.factorization p
  | 0, a, h => by
    have : a = 0 := by omega
    subst this; simp [vp]
  | k + 1, a, h => by
    unfold vp
    split_ifs with hc
    · obtain ⟨ha, hd⟩ := hc
      have hlt : a / p < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) hp.one_lt
      rw [vp_eq p hp k (a / p) (by omega)]
      rw [Nat.factorization_div hd, Finsupp.coe_tsub, Pi.sub_apply, hp.factorization_self]
      have : 1 ≤ a.factorization p := (hp.dvd_iff_one_le_factorization ha).mp hd
      omega
    · push Not at hc
      by_cases ha : a = 0
      · subst ha; simp
      · exact (Nat.factorization_eq_zero_of_not_dvd (hc ha)).symm

/-- La vérification finie : pour tout premier q ≤ 73 et tout 1 ≤ a < q. -/
def chk (q : ℕ) : Prop :=
  ∀ a ∈ Finset.range q, a = 0 ∨
    2 * a * ∏ p ∈ Pq q, p ≤ ∏ p ∈ Pq q, (1 + p ^ (1 + vp p a a)) + ∏ p ∈ Pq q, (1 + p)

instance (q : ℕ) : Decidable (chk q) := by unfold chk; infer_instance

lemma chk_all (q : ℕ) (hq73 : q ≤ 73) : chk q := by
  interval_cases q <;> decide

/-- La valuation en p de ∏_{r∈s} r^(f r) vaut f p. -/
lemma fact_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (f : ℕ → ℕ) (p : ℕ) (hp : p ∈ s) :
    (∏ r ∈ s, r ^ f r).factorization p = f p := by
  rw [Nat.factorization_prod (fun r hr => pow_ne_zero _ (hs r hr).ne_zero), Finset.sum_apply',
    Finset.sum_eq_single p]
  · rw [(hs p hp).factorization_pow, Finsupp.single_eq_same]
  · intro r hr hrp
    rw [(hs r hr).factorization_pow]
    simp [hrp]
  · intro h; exact absurd hp h

/-- Cas des premiers < q, q ≤ 73. -/
lemma KI0 (q : ℕ) (hq73 : q ≤ 73) (f : ℕ → ℕ) (hA : ∏ p ∈ Pq q, p ^ f p < q) :
    2 * ∏ p ∈ Pq q, p ^ (f p + 1) ≤ ∏ p ∈ Pq q, (1 + p ^ (f p + 1)) + ∏ p ∈ Pq q, (1 + p) := by
  have hPrime : ∀ p ∈ Pq q, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  set a := ∏ p ∈ Pq q, p ^ f p with ha
  have hfa : ∀ p ∈ Pq q, f p = vp p a a := fun p hp => by
    rw [vp_eq p (hPrime p hp) a a le_rfl, ha, fact_prod _ hPrime f p hp]
  have hpos : 0 < a := Finset.prod_pos fun p hp => pow_pos (hPrime p hp).pos _
  rcases chk_all q hq73 a (Finset.mem_range.mpr hA) with h0 | hc
  · omega
  have e1 : ∏ p ∈ Pq q, p ^ (f p + 1) = a * ∏ p ∈ Pq q, p := by
    rw [ha, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => pow_succ _ _
  have e2 : ∏ p ∈ Pq q, (1 + p ^ (f p + 1)) = ∏ p ∈ Pq q, (1 + p ^ (1 + vp p a a)) :=
    Finset.prod_congr rfl fun p hp => by rw [hfa p hp, add_comm (vp p a a)]
  rw [e1, e2, ← mul_assoc]
  exact hc

/-- **Étape 1 (petits q).** -/
theorem KI_small (S : Finset ℕ) (e : ℕ → ℕ) (q : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (he : ∀ p ∈ S, 1 ≤ e p) (hq : q.Prime) (hqS : q ∉ S)
    (hmin : ∀ p, p.Prime → p < q → p ∈ S) (hA : ∏ p ∈ S, p ^ (e p - 1) < q)
    (hq73 : q ≤ 73) :
    2 * ∏ p ∈ S, p ^ e p ≤ ∏ p ∈ S, (1 + p ^ e p) + ∏ p ∈ S, (1 + p) := by
  classical
  have h0S : Pq q ⊆ S := fun p hp =>
    hmin p (Finset.mem_filter.mp hp).2 (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  -- A restreint à Pq q
  have hA0 : ∏ p ∈ Pq q, p ^ (e p - 1) < q := by
    refine lt_of_le_of_lt ?_ hA
    apply Finset.prod_le_prod_of_subset_of_one_le h0S
    intro p hp _; exact Nat.one_le_pow _ _ (hS p hp).pos
  -- sur S \ Pq q, e = 1
  have he1 : ∀ p ∈ S \ Pq q, e p = 1 := by
    intro p hp
    obtain ⟨hpS, hpn⟩ := Finset.mem_sdiff.mp hp
    have h1 := he p hpS
    by_contra hne
    have hle : p ≤ ∏ r ∈ S, r ^ (e r - 1) :=
      calc p ≤ p ^ (e p - 1) := Nat.le_self_pow (by omega) p
        _ ≤ ∏ r ∈ S, r ^ (e r - 1) :=
          Finset.single_le_prod (f := fun r => r ^ (e r - 1))
            (fun r hr => Nat.one_le_pow _ _ (hS r hr).pos) hpS
    exact hpn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hS p hpS⟩)
  have h0 := KI0 q hq73 (fun p => e p - 1) hA0
  have hadd : ∀ p ∈ Pq q, e p - 1 + 1 = e p := fun p hp => Nat.sub_add_cancel (he p (h0S hp))
  have e1 : ∏ p ∈ Pq q, p ^ (e p - 1 + 1) = ∏ p ∈ Pq q, p ^ e p :=
    Finset.prod_congr rfl fun p hp => by rw [hadd p hp]
  have e2 : ∏ p ∈ Pq q, (1 + p ^ (e p - 1 + 1)) = ∏ p ∈ Pq q, (1 + p ^ e p) :=
    Finset.prod_congr rfl fun p hp => by rw [hadd p hp]
  rw [e1, e2] at h0
  -- découpage S = (S \ Pq q) ∪ Pq q
  rw [← Finset.prod_sdiff h0S, ← Finset.prod_sdiff (f := fun p => 1 + p ^ e p) h0S,
    ← Finset.prod_sdiff (f := fun p => 1 + p) h0S]
  have hX : ∏ p ∈ S \ Pq q, p ^ e p = ∏ p ∈ S \ Pq q, p :=
    Finset.prod_congr rfl fun p hp => by rw [he1 p hp, pow_one]
  have hY : ∏ p ∈ S \ Pq q, (1 + p ^ e p) = ∏ p ∈ S \ Pq q, (1 + p) :=
    Finset.prod_congr rfl fun p hp => by rw [he1 p hp, pow_one]
  have hXY : ∏ p ∈ S \ Pq q, p ≤ ∏ p ∈ S \ Pq q, (1 + p) :=
    Finset.prod_le_prod fun p _ => Nat.le_add_left p 1
  rw [hX, hY]
  set X := ∏ p ∈ S \ Pq q, p
  set Y := ∏ p ∈ S \ Pq q, (1 + p)
  set G := ∏ p ∈ Pq q, p ^ e p
  set H := ∏ p ∈ Pq q, (1 + p ^ e p)
  set K := ∏ p ∈ Pq q, (1 + p)
  calc 2 * (X * G) = X * (2 * G) := by ring
    _ ≤ Y * (H + K) := Nat.mul_le_mul hXY h0
    _ = Y * H + Y * K := by ring


/-! ## Étapes 2 et 3 : lemmes de rangement -/



lemma card_Pq_nth (t : ℕ) : (Pq (Nat.nth Nat.Prime t)).card = t := by
  rw [Pq, ← Nat.count_eq_card_filter_range]
  exact Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime t

/-- Données communes : R = premiers < p_t, avec |R| = |T|. -/
lemma ord_data (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    let b := Nat.nth Nat.Prime T.card
    (T \ Pq b).card = (Pq b \ T).card ∧ 0 < b ∧
    (∀ p ∈ T \ Pq b, b ≤ p) ∧ (∀ r ∈ Pq b \ T, r < b) ∧ (∀ r ∈ Pq b, 0 < r) := by
  intro b
  refine ⟨Finset.card_sdiff_comm (card_Pq_nth T.card).symm, (Nat.prime_nth_prime T.card).pos, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpT, hpR⟩ := Finset.mem_sdiff.mp hp
    by_contra h
    push Not at h
    exact hpR (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hT p hpT⟩)
  · intro r hr
    exact Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).1
  · intro r hr
    exact (Finset.mem_filter.mp hr).2.pos

lemma K_ord1 (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ∏ p ∈ T, (1 + 1 / (p : ℚ)) ≤ ∏ p ∈ Pq (Nat.nth Nat.Prime T.card), (1 + 1 / (p : ℚ)) := by
  classical
  obtain ⟨hk, hb0, hTR, hRT, hRpos⟩ := ord_data T hT
  set b := Nat.nth Nat.Prime T.card
  set R := Pq b
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb0
  have h1 : ∏ p ∈ T \ R, (1 + 1 / (p : ℚ)) ≤ (1 + 1 / (b : ℚ)) ^ (R \ T).card := by
    rw [← hk, ← Finset.prod_const]
    gcongr with p hp
    exact_mod_cast hTR p hp
  have h2 : (1 + 1 / (b : ℚ)) ^ (R \ T).card ≤ ∏ r ∈ R \ T, (1 + 1 / (r : ℚ)) := by
    rw [← Finset.prod_const]
    gcongr with r hr
    · exact_mod_cast hRpos r (Finset.mem_sdiff.mp hr).1
    · exact_mod_cast (hRT r hr).le
  calc ∏ p ∈ T, (1 + 1 / (p : ℚ))
      = (∏ p ∈ T ∩ R, (1 + 1 / (p : ℚ))) * ∏ p ∈ T \ R, (1 + 1 / (p : ℚ)) :=
        (Finset.prod_inter_mul_prod_sdiff T R _).symm
    _ ≤ (∏ p ∈ T ∩ R, (1 + 1 / (p : ℚ))) * ∏ r ∈ R \ T, (1 + 1 / (r : ℚ)) := by
        exact mul_le_mul_of_nonneg_left (h1.trans h2) (Finset.prod_nonneg fun _ _ => by positivity)
    _ = ∏ p ∈ R, (1 + 1 / (p : ℚ)) := by
        rw [Finset.inter_comm, Finset.prod_inter_mul_prod_sdiff]

lemma K_ord2 (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ∏ p ∈ Pq (Nat.nth Nat.Prime T.card), p ≤ ∏ p ∈ T, p := by
  classical
  obtain ⟨hk, hb0, hTR, hRT, hRpos⟩ := ord_data T hT
  set b := Nat.nth Nat.Prime T.card
  set R := Pq b
  have h1 : ∏ r ∈ R \ T, r ≤ b ^ (T \ R).card := by
    rw [hk, ← Finset.prod_const]
    exact Finset.prod_le_prod fun r hr => (hRT r hr).le
  have h2 : b ^ (T \ R).card ≤ ∏ p ∈ T \ R, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod fun p hp => hTR p hp
  calc ∏ p ∈ R, p = (∏ p ∈ R ∩ T, p) * ∏ p ∈ R \ T, p := (Finset.prod_inter_mul_prod_sdiff R T _).symm
    _ ≤ (∏ p ∈ R ∩ T, p) * ∏ p ∈ T \ R, p := Nat.mul_le_mul_left _ (h1.trans h2)
    _ = ∏ p ∈ T, p := by rw [Finset.inter_comm, Finset.prod_inter_mul_prod_sdiff]


/-! ## Étape 4 : le cœur analytique -/



/-- P_t et D_t : produit des t premiers nombres premiers, et de leurs (1 + 1/p). -/
noncomputable def Pt (t : ℕ) : ℕ := ∏ p ∈ Pq (Nat.nth Nat.Prime t), p
noncomputable def Dt (t : ℕ) : ℚ := ∏ p ∈ Pq (Nat.nth Nat.Prime t), (1 + 1 / (p : ℚ))

lemma nth_prime_lt (t : ℕ) : Nat.nth Nat.Prime t < Nat.nth Nat.Prime (t + 1) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self t)

lemma not_mem_Pq_self (a : ℕ) : a ∉ Pq a := by simp [Pq]

lemma Pq_succ (t : ℕ) :
    Pq (Nat.nth Nat.Prime (t + 1)) = insert (Nat.nth Nat.Prime t) (Pq (Nat.nth Nat.Prime t)) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (nth_prime_lt t), Nat.prime_nth_prime t⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((Finset.mem_range.mp h1).trans (nth_prime_lt t)), h2⟩
  · rw [Finset.card_insert_of_notMem (not_mem_Pq_self _), card_Pq_nth, card_Pq_nth]

lemma Pt_succ (t : ℕ) : Pt (t + 1) = Nat.nth Nat.Prime t * Pt t := by
  rw [Pt, Pq_succ, Finset.prod_insert (not_mem_Pq_self _)]; rfl

lemma Dt_succ (t : ℕ) : Dt (t + 1) = (1 + 1 / (Nat.nth Nat.Prime t : ℚ)) * Dt t := by
  rw [Dt, Pq_succ, Finset.prod_insert (not_mem_Pq_self _)]; rfl

lemma Dt_nonneg (t : ℕ) : 0 ≤ Dt t := Finset.prod_nonneg fun p _ => by positivity

/-- D_t ≤ (t+2)/2. -/
lemma Dt_le (t : ℕ) : Dt t ≤ ((t : ℚ) + 2) / 2 := by
  induction t with
  | zero =>
    have : Pq 2 = ∅ := by decide
    simp [Dt, Nat.nth_prime_zero_eq_two, this]
  | succ t ih =>
    rw [Dt_succ]
    have hp : (t : ℚ) + 2 ≤ (Nat.nth Nat.Prime t : ℚ) := by exact_mod_cast Nat.add_two_le_nth_prime t
    have h1 : 1 + 1 / (Nat.nth Nat.Prime t : ℚ) ≤ 1 + 1 / ((t : ℚ) + 2) := by gcongr
    calc (1 + 1 / (Nat.nth Nat.Prime t : ℚ)) * Dt t
        ≤ (1 + 1 / ((t : ℚ) + 2)) * (((t : ℚ) + 2) / 2) :=
          mul_le_mul h1 ih (Dt_nonneg t) (by positivity)
      _ = (((t + 1 : ℕ) : ℚ) + 2) / 2 := by push_cast; field_simp; ring

/-! ## Série harmonique -/

lemma harmonic_mono' (m k : ℕ) : harmonic m ≤ harmonic (m + k) := by
  simp only [harmonic, Finset.sum_range_add]
  have : 0 ≤ ∑ x ∈ Finset.range k, ((↑(m + x + 1) : ℚ))⁻¹ := Finset.sum_nonneg fun _ _ => by positivity
  linarith

lemma harmonic_mono_le {m n : ℕ} (h : m ≤ n) : harmonic m ≤ harmonic n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact harmonic_mono' m k

lemma harmonic_double (N : ℕ) (hN : 1 ≤ N) : harmonic N + 1 / 2 ≤ harmonic (2 * N) := by
  rw [two_mul]
  simp only [harmonic, Finset.sum_range_add]
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have : ∑ _x ∈ Finset.range N, (1 / (2 * (N : ℚ))) ≤ ∑ x ∈ Finset.range N, ((↑(N + x + 1) : ℚ))⁻¹ := by
    apply Finset.sum_le_sum
    intro x hx
    have hx' : x + 1 ≤ N := Finset.mem_range.mp hx
    rw [one_div]
    apply inv_anti₀ (by positivity)
    push_cast
    have : (x : ℚ) + 1 ≤ N := by exact_mod_cast hx'
    linarith
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have h2 : (N : ℚ) * (1 / (2 * N)) = 1 / 2 := by field_simp
  linarith

lemma harmonic_pow_two (m : ℕ) : 1 + (m : ℚ) / 2 ≤ harmonic (2 ^ m) := by
  induction m with
  | zero => simp [harmonic]
  | succ m ih =>
    rw [pow_succ, mul_comm]
    have := harmonic_double (2 ^ m) (Nat.one_le_two_pow)
    push_cast
    linarith

lemma harmonic_sixteen (N : ℕ) (hN : 1 ≤ N) : harmonic N + 2 ≤ harmonic (16 * N) := by
  have h1 := harmonic_double N hN
  have h2 := harmonic_double (2 * N) (by omega)
  have h3 := harmonic_double (2 * (2 * N)) (by omega)
  have h4 := harmonic_double (2 * (2 * (2 * N))) (by omega)
  have : 2 * (2 * (2 * (2 * N))) = 16 * N := by ring
  rw [this] at h4
  linarith

/-! ## Base t = 10 -/

lemma nth_prime_ten : Nat.nth Nat.Prime 10 = 31 := by
  have h : Nat.count Nat.Prime 31 = 10 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma Pq_31 : Pq 31 = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by decide

lemma Pt_ten : Pt 10 = 6469693230 := by rw [Pt, nth_prime_ten, Pq_31]; rfl

lemma Dt_ten : Dt 10 = ∏ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), (1 + 1 / (p : ℚ)) := by
  rw [Dt, nth_prime_ten, Pq_31]

lemma base_ten : 4 * Dt 10 ≤ harmonic (Pt 10) := by
  have h1 : 1 + ((32 : ℕ) : ℚ) / 2 ≤ harmonic (2 ^ 32) := harmonic_pow_two 32
  have h2 : harmonic (2 ^ 32) ≤ harmonic (Pt 10) := harmonic_mono_le (by rw [Pt_ten]; norm_num)
  have hc : (1 : ℚ) + ((32 : ℕ) : ℚ) / 2 = 17 := by norm_num
  have h3 : 4 * Dt 10 ≤ 17 := by
    rw [Dt_ten]; simp [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton]; norm_num
  calc 4 * Dt 10 ≤ 17 := h3
    _ = 1 + ((32 : ℕ) : ℚ) / 2 := hc.symm
    _ ≤ harmonic (2 ^ 32) := h1
    _ ≤ harmonic (Pt 10) := h2

/-- (★) Pour t ≥ 10 : 4·D_t ≤ H(P_t). -/
lemma star (t : ℕ) (ht : 10 ≤ t) : 4 * Dt t ≤ harmonic (Pt t) := by
  induction t, ht using Nat.le_induction with
  | base => exact base_ten
  | succ t ht ih =>
    set p := Nat.nth Nat.Prime t with hpdef
    have hp31 : 31 ≤ p := by
      rw [hpdef, ← nth_prime_ten]
      exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone ht
    have hpt : (t : ℚ) + 2 ≤ (p : ℚ) := by exact_mod_cast Nat.add_two_le_nth_prime t
    have hpq : (0 : ℚ) < p := by positivity
    have hD := Dt_le t
    have hD0 := Dt_nonneg t
    have hPt0 : 0 < Pt t := by
      unfold Pt; apply Finset.prod_pos; intro q hq; exact Nat.Prime.pos (Finset.mem_filter.mp hq).2
    have hPt : 1 ≤ Pt t := hPt0
    rw [Dt_succ, Pt_succ]
    have hstep : 4 * ((1 + 1 / (p : ℚ)) * Dt t) ≤ 4 * Dt t + 2 := by
      have : 4 * Dt t / p ≤ 2 := by
        rw [div_le_iff₀ hpq]; linarith
      have e : 4 * ((1 + 1 / (p : ℚ)) * Dt t) = 4 * Dt t + 4 * Dt t / p := by field_simp
      linarith
    have h16 := harmonic_sixteen (Pt t) hPt
    have hmono : harmonic (16 * Pt t) ≤ harmonic (p * Pt t) :=
      harmonic_mono_le (Nat.mul_le_mul_right _ (by omega))
    linarith

/-! ## Lemme H1 : N(q) ≥ H(q−1)/2 -/

def SQ (x : ℕ) : Finset ℕ := (Finset.Icc 1 x).filter Squarefree
noncomputable def Ssum (x : ℕ) : ℚ := ∑ d ∈ SQ x, 1 / (d : ℚ)


lemma Nq_ge_S (q : ℕ) : Ssum (q - 1) ≤ Nq q := by
  classical
  unfold Nq Ssum
  rw [Finset.prod_one_add]
  have hprod : ∀ d ∈ SQ (q - 1), ∏ p ∈ d.primeFactors, p = d := fun d hd =>
    Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd).2
  have hinj : Set.InjOn Nat.primeFactors ↑(SQ (q - 1)) := by
    intro d hd d' hd' h
    rw [← hprod d hd, ← hprod d' hd']
    exact congrArg (fun t => ∏ p ∈ t, p) h
  have hval : ∀ d ∈ SQ (q - 1), 1 / (d : ℚ) = ∏ p ∈ d.primeFactors, 1 / (p : ℚ) := by
    intro d hd
    calc 1 / (d : ℚ) = 1 / (((∏ p ∈ d.primeFactors, p : ℕ)) : ℚ) := by rw [hprod d hd]
      _ = ∏ p ∈ d.primeFactors, 1 / (p : ℚ) := by
          rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]; simp [one_div]
  rw [Finset.sum_congr rfl hval,
    ← Finset.sum_image (f := fun t : Finset ℕ => ∏ p ∈ t, 1 / (p : ℚ)) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_powerset]
    intro p hp
    have hdx := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    have hpd : p ≤ d := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_of_mem_primeFactors hp⟩
  · intro t _ _
    exact Finset.prod_nonneg fun p _ => by positivity

lemma harmonic_le_two_S (x : ℕ) : harmonic x ≤ 2 * Ssum x := by
  classical
  rw [harmonic_eq_sum_Icc]
  have hex : ∀ n ∈ Finset.Icc 1 x, ∃ ab : ℕ × ℕ,
      0 < ab.1 ∧ 0 < ab.2 ∧ ab.2 ^ 2 * ab.1 = n ∧ Squarefree ab.1 := by
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    obtain ⟨a, b, ha, hb, h, hs⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < n by omega)
    exact ⟨(a, b), ha, hb, h, hs⟩
  choose! φ hφ using hex
  have hinj : Set.InjOn φ ↑(Finset.Icc 1 x) := by
    intro n hn m hm h
    have e1 := (hφ n hn).2.2.1
    have e2 := (hφ m hm).2.2.1
    rw [← e1, ← e2, h]
  have hval : ∀ n ∈ Finset.Icc 1 x,
      ((n : ℚ))⁻¹ = 1 / (((φ n).1 : ℚ) * ((φ n).2 : ℚ) ^ 2) := by
    intro n hn
    obtain ⟨-, -, e, -⟩ := hφ n hn
    have e' : (n : ℚ) = ((φ n).2 : ℚ) ^ 2 * ((φ n).1 : ℚ) := by exact_mod_cast e.symm
    rw [e', one_div]; ring
  rw [Finset.sum_congr rfl hval,
    ← Finset.sum_image (f := fun ab : ℕ × ℕ => 1 / ((ab.1 : ℚ) * (ab.2 : ℚ) ^ 2)) hinj]
  have hsub : (Finset.Icc 1 x).image φ ⊆ SQ x ×ˢ Finset.Icc 1 x := by
    intro ab hab
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hab
    obtain ⟨ha, hb, e, hs⟩ := hφ n hn
    have hnx := Finset.mem_Icc.mp hn
    have h1 : (φ n).1 ≤ n := by
      calc (φ n).1 ≤ (φ n).2 ^ 2 * (φ n).1 := Nat.le_mul_of_pos_left _ (by positivity)
        _ = n := e
    have h2 : (φ n).2 ≤ n := by
      calc (φ n).2 ≤ (φ n).2 ^ 2 * (φ n).1 := by nlinarith
        _ = n := e
    simp only [Finset.mem_product, SQ, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨ha, by omega⟩, hs⟩, hb, by omega⟩
  have hsq : ∑ b ∈ Finset.Icc 1 x, 1 / (b : ℚ) ^ 2 ≤ 2 := by
    have h := sum_Ioo_inv_sq_le (α := ℚ) 0 (x + 1)
    have hI : Finset.Ioo 0 (x + 1) = Finset.Icc 1 x := by ext; simp; omega
    rw [hI] at h
    simpa [one_div] using h
  calc ∑ ab ∈ (Finset.Icc 1 x).image φ, 1 / ((ab.1 : ℚ) * (ab.2 : ℚ) ^ 2)
      ≤ ∑ ab ∈ SQ x ×ˢ Finset.Icc 1 x, 1 / ((ab.1 : ℚ) * (ab.2 : ℚ) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑ a ∈ SQ x, 1 / (a : ℚ)) * ∑ b ∈ Finset.Icc 1 x, 1 / (b : ℚ) ^ 2 := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        rw [one_div_mul_one_div]
    _ ≤ Ssum x * 2 :=
        mul_le_mul_of_nonneg_left hsq (Finset.sum_nonneg fun _ _ => by positivity)
    _ = 2 * Ssum x := by ring

/-- **H1** : N(q) ≥ H(q−1)/2. -/
lemma Nq_ge_harmonic (q : ℕ) : harmonic (q - 1) / 2 ≤ Nq q := by
  have h1 := harmonic_le_two_S (q - 1)
  have h2 := Nq_ge_S q
  linarith

/-- Queue : t ≥ 10 et P_t < q ⇒ 2·D_t ≤ N(q). -/
lemma tail (t q : ℕ) (ht : 10 ≤ t) (h : Pt t < q) : 2 * Dt t ≤ Nq q := by
  have h1 := star t ht
  have h2 : harmonic (Pt t) ≤ harmonic (q - 1) := harmonic_mono_le (by omega)
  have h3 := Nq_ge_harmonic q
  linarith




lemma one_le_f (p : ℕ) : (1 : ℚ) ≤ 1 + 1 / (p : ℚ) := by
  have : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
  linarith

lemma Nq_mono {y q : ℕ} (h : y ≤ q) : Nq y ≤ Nq q := by
  apply prodQ_mono _ (fun p _ => one_le_f p)
  intro p hp
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp h1) h), h2⟩

lemma Nq_ge_list (y : ℕ) (L : List ℕ) (hnd : L.Nodup) (hL : ∀ p ∈ L, p.Prime ∧ p < y) :
    (L.map (fun p : ℕ => 1 + 1 / (p : ℚ))).prod ≤ Nq y := by
  rw [← List.prod_toFinset _ hnd]
  apply prodQ_mono _ (fun p _ => one_le_f p)
  intro p hp
  rw [List.mem_toFinset] at hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hL p hp).2, (hL p hp).1⟩

lemma nth_val (t b : ℕ) (hb : b.Prime) (hc : Nat.count Nat.Prime b = t) :
    Nat.nth Nat.Prime t = b := by
  rw [← hc]; exact Nat.nth_count hb

/-- Un cas t ≤ 9 : D_t calculé sur la liste R, N(q) minoré par la liste L. -/
lemma small_case (t b y : ℕ) (R L : List ℕ) (hb : b.Prime) (hc : Nat.count Nat.Prime b = t)
    (hR : Pq b = R.toFinset) (hRnd : R.Nodup) (hnd : L.Nodup) (hL : ∀ p ∈ L, p.Prime ∧ p < y)
    (hnum : 2 * (R.map (fun p : ℕ => 1 + 1 / (p : ℚ))).prod ≤ (L.map (fun p : ℕ => 1 + 1 / (p : ℚ))).prod)
    (q : ℕ) (hq : y ≤ q) : 2 * Dt t ≤ Nq q := by
  rw [Dt, nth_val t b hb hc, hR, List.prod_toFinset _ hRnd]
  exact hnum.trans ((Nq_ge_list y L hnd hL).trans (Nq_mono hq))

lemma Pt_val (t b : ℕ) (R : List ℕ) (hb : b.Prime) (hc : Nat.count Nat.Prime b = t)
    (hR : Pq b = R.toFinset) (hRnd : R.Nodup) : Pt t = R.prod := by
  rw [Pt, nth_val t b hb hc, hR, List.prod_toFinset _ hRnd]
  simp

def L74 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]
def L150 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149]
def L234 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233]
def L368 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367]
def L522 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521]
def L734 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733]
def L992 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991]
def R2 : List ℕ := []
def R3 : List ℕ := [2]
def R5 : List ℕ := [2, 3]
def R7 : List ℕ := [2, 3, 5]
def R11 : List ℕ := [2, 3, 5, 7]
def R13 : List ℕ := [2, 3, 5, 7, 11]
def R17 : List ℕ := [2, 3, 5, 7, 11, 13]
def R19 : List ℕ := [2, 3, 5, 7, 11, 13, 17]
def R23 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19]
def R29 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23]

lemma hL74 : ∀ p ∈ L74, p.Prime ∧ p < 74 := by
  simp only [L74, List.forall_mem_cons]; norm_num
lemma hL150 : ∀ p ∈ L150, p.Prime ∧ p < 150 := by
  simp only [L150, List.forall_mem_cons]; norm_num
lemma hL234 : ∀ p ∈ L234, p.Prime ∧ p < 234 := by
  simp only [L234, List.forall_mem_cons]; norm_num
lemma hL368 : ∀ p ∈ L368, p.Prime ∧ p < 368 := by
  simp only [L368, List.forall_mem_cons]; norm_num
lemma hL522 : ∀ p ∈ L522, p.Prime ∧ p < 522 := by
  simp only [L522, List.forall_mem_cons]; norm_num
lemma hL734 : ∀ p ∈ L734, p.Prime ∧ p < 734 := by
  simp only [L734, List.forall_mem_cons]; norm_num
set_option maxRecDepth 100000 in
lemma hL992 : ∀ p ∈ L992, p.Prime ∧ p < 992 := by
  simp only [L992, List.forall_mem_cons]; norm_num

set_option maxRecDepth 100000

lemma case0 (q : ℕ) (hq : 74 ≤ q) : 2 * Dt 0 ≤ Nq q :=
  small_case 0 2 74 R2 L74 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL74
    (by simp only [R2, L74, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

lemma case1 (q : ℕ) (hq : 74 ≤ q) : 2 * Dt 1 ≤ Nq q :=
  small_case 1 3 74 R3 L74 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL74
    (by simp only [R3, L74, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

lemma case2 (q : ℕ) (hq : 74 ≤ q) : 2 * Dt 2 ≤ Nq q :=
  small_case 2 5 74 R5 L74 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL74
    (by simp only [R5, L74, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

lemma case3 (q : ℕ) (hq : 74 ≤ q) : 2 * Dt 3 ≤ Nq q :=
  small_case 3 7 74 R7 L74 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL74
    (by simp only [R7, L74, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

lemma case4 (q : ℕ) (hq : 150 ≤ q) : 2 * Dt 4 ≤ Nq q :=
  small_case 4 11 150 R11 L150 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL150
    (by simp only [R11, L150, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

lemma case5 (q : ℕ) (hq : 234 ≤ q) : 2 * Dt 5 ≤ Nq q :=
  small_case 5 13 234 R13 L234 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL234
    (by simp only [R13, L234, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

lemma case6 (q : ℕ) (hq : 368 ≤ q) : 2 * Dt 6 ≤ Nq q :=
  small_case 6 17 368 R17 L368 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL368
    (by simp only [R17, L368, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

lemma case7 (q : ℕ) (hq : 522 ≤ q) : 2 * Dt 7 ≤ Nq q :=
  small_case 7 19 522 R19 L522 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL522
    (by simp only [R19, L522, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

lemma case8 (q : ℕ) (hq : 734 ≤ q) : 2 * Dt 8 ≤ Nq q :=
  small_case 8 23 734 R23 L734 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL734
    (by simp only [R23, L734, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

lemma case9 (q : ℕ) (hq : 992 ≤ q) : 2 * Dt 9 ≤ Nq q :=
  small_case 9 29 992 R29 L992 (by norm_num) (by decide) (by decide) (by decide) (by decide) hL992
    (by simp only [R29, L992, List.map, List.prod_cons, List.prod_nil]; norm_num) q hq

/-- **Étape 4, cas t ≤ 9.** -/
lemma K_num_small (t q : ℕ) (ht : t ≤ 9) (hq : 73 < q) (h : Pt t < q) : 2 * Dt t ≤ Nq q := by
  interval_cases t
  · exact case0 q (by omega)
  · exact case1 q (by omega)
  · exact case2 q (by omega)
  · exact case3 q (by omega)
  · rw [Pt_val 4 11 R11 (by norm_num) (by decide) (by decide) (by decide)] at h
    norm_num [R11] at h
    exact case4 q (by omega)
  · rw [Pt_val 5 13 R13 (by norm_num) (by decide) (by decide) (by decide)] at h
    norm_num [R13] at h
    exact case5 q (by omega)
  · rw [Pt_val 6 17 R17 (by norm_num) (by decide) (by decide) (by decide)] at h
    norm_num [R17] at h
    exact case6 q (by omega)
  · rw [Pt_val 7 19 R19 (by norm_num) (by decide) (by decide) (by decide)] at h
    norm_num [R19] at h
    exact case7 q (by omega)
  · rw [Pt_val 8 23 R23 (by norm_num) (by decide) (by decide) (by decide)] at h
    norm_num [R23] at h
    exact case8 q (by omega)
  · rw [Pt_val 9 29 R29 (by norm_num) (by decide) (by decide) (by decide)] at h
    norm_num [R29] at h
    exact case9 q (by omega)


/-- **Étape 4.** Si P_t < q et q > 73, alors 2·D_t ≤ N(q). -/
lemma K_num (t q : ℕ) (hq : 73 < q) (h : ∏ p ∈ Pq (Nat.nth Nat.Prime t), p < q) :
    2 * ∏ p ∈ Pq (Nat.nth Nat.Prime t), (1 + 1 / (p : ℚ)) ≤ Nq q := by
  rcases le_or_gt t 9 with h9 | h9
  · exact K_num_small t q h9 hq h
  · exact tail t q (by omega) h

/-! ## Assemblage (démontré) -/

/-- Lemme K : pour q > 73, retirer un ensemble T de produit < q laisse un produit ≥ 2. -/
lemma K (q : ℕ) (hq : 73 < q) (T : Finset ℕ) (hTq : T ⊆ Pq q) (hTprod : ∏ p ∈ T, p < q) :
    2 ≤ ∏ p ∈ Pq q \ T, (1 + 1 / (p : ℚ)) := by
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => (Finset.mem_filter.mp (hTq hp)).2
  have hpos : 0 < ∏ p ∈ T, (1 + 1 / (p : ℚ)) := Finset.prod_pos fun p _ => by positivity
  have h1 := K_ord1 T hTp
  have h2 := K_num T.card q hq (lt_of_le_of_lt (K_ord2 T hTp) hTprod)
  have hsplit : (∏ p ∈ Pq q \ T, (1 + 1 / (p : ℚ))) * ∏ p ∈ T, (1 + 1 / (p : ℚ)) = Nq q :=
    Finset.prod_sdiff hTq
  have : 2 * ∏ p ∈ T, (1 + 1 / (p : ℚ)) ≤ (∏ p ∈ Pq q \ T, (1 + 1 / (p : ℚ))) * ∏ p ∈ T, (1 + 1 / (p : ℚ)) := by
    rw [hsplit]; linarith
  exact le_of_mul_le_mul_right this hpos

/-- Grands q : usigma seul suffit. -/
theorem KI_large (S : Finset ℕ) (e : ℕ → ℕ) (q : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (he : ∀ p ∈ S, 1 ≤ e p)
    (hmin : ∀ p, p.Prime → p < q → p ∈ S) (hA : ∏ p ∈ S, p ^ (e p - 1) < q)
    (hq73 : 73 < q) :
    2 * ∏ p ∈ S, p ^ e p ≤ ∏ p ∈ S, (1 + p ^ e p) := by
  classical
  set T := S.filter (fun p => 2 ≤ e p) with hTdef
  have hTS : T ⊆ S := Finset.filter_subset _ _
  -- ∏_T p ≤ ∏_S p^(e-1) < q
  have hTprod : ∏ p ∈ T, p < q := by
    refine lt_of_le_of_lt ?_ hA
    calc ∏ p ∈ T, p ≤ ∏ p ∈ T, p ^ (e p - 1) := by
          apply Finset.prod_le_prod ; intro p hp
          have h2 := (Finset.mem_filter.mp hp).2
          exact Nat.le_self_pow (by omega) p
      _ ≤ ∏ p ∈ S, p ^ (e p - 1) := by
          apply Finset.prod_le_prod_of_subset_of_one_le hTS
          intro p hp _
          exact Nat.one_le_pow _ _ (hS p hp).pos
  have hTq : T ⊆ Pq q := by
    intro p hp
    have hpp := hS p (hTS hp)
    have : p ≤ ∏ p ∈ T, p := Finset.single_le_prod (fun i hi => (hS i (hTS hi)).one_le) hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩
  have hK := K q hq73 T hTq hTprod
  -- Pq \ T ⊆ S \ T, et sur S \ T, e = 1
  have hsub : Pq q \ T ⊆ S \ T := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hr, hpr⟩ := Finset.mem_filter.mp hp1
    exact Finset.mem_sdiff.mpr ⟨hmin p hpr (Finset.mem_range.mp hr), hp2⟩
  have he1 : ∀ p ∈ S \ T, e p = 1 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hp
    have := he p h1
    by_contra hne
    exact h2 (Finset.mem_filter.mpr ⟨h1, by omega⟩)
  -- passage aux rationnels
  have hppos : ∀ p ∈ S, (0 : ℚ) < (p : ℚ) ^ e p := fun p hp => by
    have := (hS p hp).pos; positivity
  have key : (2 : ℚ) ≤ ∏ p ∈ S, (1 + 1 / (p : ℚ) ^ e p) := by
    calc (2 : ℚ) ≤ ∏ p ∈ Pq q \ T, (1 + 1 / (p : ℚ)) := hK
      _ ≤ ∏ p ∈ S \ T, (1 + 1 / (p : ℚ)) := by
          apply prodQ_mono hsub
          intro p _; have : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
          linarith
      _ = ∏ p ∈ S \ T, (1 + 1 / (p : ℚ) ^ e p) := by
          apply Finset.prod_congr rfl; intro p hp; rw [he1 p hp, pow_one]
      _ ≤ ∏ p ∈ S, (1 + 1 / (p : ℚ) ^ e p) := by
          apply prodQ_mono Finset.sdiff_subset
          intro p _; have : (0 : ℚ) ≤ 1 / (p : ℚ) ^ e p := by positivity
          linarith
  have hprodpos : (0 : ℚ) < ∏ p ∈ S, (p : ℚ) ^ e p := Finset.prod_pos hppos
  have hfac : ∏ p ∈ S, (1 + (p : ℚ) ^ e p) = (∏ p ∈ S, (1 + 1 / (p : ℚ) ^ e p)) * ∏ p ∈ S, (p : ℚ) ^ e p := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro p hp
    have := (hppos p hp).ne'
    field_simp
    ring
  have hQ : (2 : ℚ) * ∏ p ∈ S, (p : ℚ) ^ e p ≤ ∏ p ∈ S, (1 + (p : ℚ) ^ e p) := by
    rw [hfac]; exact mul_le_mul_of_nonneg_right key hprodpos.le
  exact_mod_cast hQ

/-- L'inégalité clé, tous q confondus. -/
theorem KI (S : Finset ℕ) (e : ℕ → ℕ) (q : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (he : ∀ p ∈ S, 1 ≤ e p) (hq : q.Prime) (hqS : q ∉ S)
    (hmin : ∀ p, p.Prime → p < q → p ∈ S) (hA : ∏ p ∈ S, p ^ (e p - 1) < q) :
    2 * ∏ p ∈ S, p ^ e p ≤ ∏ p ∈ S, (1 + p ^ e p) + ∏ p ∈ S, (1 + p) := by
  rcases le_or_gt q 73 with h | h
  · exact KI_small S e q hS he hq hqS hmin hA h
  · exact le_add_right (KI_large S e q hS he hmin hA h)

/-- **La conjecture A401714 ≤ A401715.** -/
theorem conjecture (n q : ℕ) (hn : 0 < n)
    (hq : q.Prime) (hqn : ¬ q ∣ n)
    (hmin : ∀ p : ℕ, p.Prime → p < q → p ∣ n)
    (hA : n / rad n < q) :
    2 * n ≤ usigma n + ssq n := by
  have hn0 : n ≠ 0 := hn.ne'
  have hS : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have he : ∀ p ∈ n.primeFactors, 1 ≤ n.factorization p := fun p hp =>
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization]))
  have hqS : q ∉ n.primeFactors := fun h => hqn (Nat.dvd_of_mem_primeFactors h)
  have hmin' : ∀ p, p.Prime → p < q → p ∈ n.primeFactors := fun p hp hpq =>
    Nat.mem_primeFactors.mpr ⟨hp, hmin p hp hpq, hn0⟩
  rw [div_rad n hn0] at hA
  have := KI n.primeFactors n.factorization q hS he hq hqS hmin' hA
  rw [n_eq_prod n hn0] at this
  exact this.trans (somme_ge n hn0)

/-! ## Forme OEIS exacte : q = A053669(n), le plus petit premier ne divisant pas n -/

lemma exists_prime_not_dvd (n : ℕ) (hn : 0 < n) : ∃ p, p.Prime ∧ ¬ p ∣ n := by
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, hp2, fun h => by have := Nat.le_of_dvd hn h; omega⟩

/-- A053669(n) : plus petit nombre premier qui ne divise pas n. -/
noncomputable def A053669 (n : ℕ) : ℕ :=
  if hn : 0 < n then Nat.find (exists_prime_not_dvd n hn) else 2

/-- A003557(n) = n / rad(n). -/
noncomputable def A003557 (n : ℕ) : ℕ := n / rad n

/-- **A401714(n) ≤ A401715(n)** pour tout n ≥ 1 : si A003557(n) < A053669(n),
alors usigma(n) + ssq(n) ≥ 2n. -/
theorem A401714_le_A401715 (n : ℕ) (hn : 0 < n) (h : A003557 n < A053669 n) :
    2 * n ≤ usigma n + ssq n := by
  unfold A053669 at h
  rw [dif_pos hn] at h
  have hspec := Nat.find_spec (exists_prime_not_dvd n hn)
  refine conjecture n _ hn hspec.1 hspec.2 ?_ h
  intro p hp hpq
  by_contra hd
  exact Nat.find_min (exists_prime_not_dvd n hn) hpq ⟨hp, hd⟩

end A401714

#print axioms A401714.conjecture
#print axioms A401714.A401714_le_A401715
