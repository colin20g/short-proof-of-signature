(** The present text gives a short proof (self contained and in less than 300 lines including
    this comment) in COQ the basic invariant result that allows to define the signature of 
    a permutation.

     Let p, q be two lists whose elements are integers, with p having distincts elements. 
     We assume there is a permutation giving q from p in an even  number of elementary steps.
     Then any other permutation givinq q from p has an even number of steps. The same occurs 
     of course if you replace even with odd.   
   Here, by "elementary step" we mean that two consecutive tems in the list are swapped.
   This is entirely sufficient for difining the signature of a permutation because 
   transposition of consecutive terms in the ordered set {1,...,n} generate all the 
   symmetric group (in layman terms, using only elementary permutations as defined above,
   you could easily rearrange any list in the order you wish and this fact is intuitively 
   obvious).*)

Section equalities_and_inequalities_tests.

  Fixpoint nat_eq_dec (x y:nat) {struct x}: sumbool (x = y) (x <> y).
  Proof.
    destruct x. destruct y. left; reflexivity. right; discriminate. destruct y.
    right; discriminate. destruct (nat_eq_dec x y). left; apply eq_S; assumption.
    right; intro F; apply n; apply eq_add_S; assumption.
  Defined.

  Fixpoint nat_le_dec (x y:nat) {struct x}: sumbool (x <= y) (~ x <= y).
  Proof.
    destruct x. left; apply le_0_n. destruct y. right; intro F; inversion F.
    destruct (nat_le_dec x y). left; apply le_n_S; assumption.
    right; intro F; apply n; apply le_S_n; assumption.
  Defined.

  Definition nat_lt_dec (x y:nat): sumbool (x < y) (~ x < y).
  Proof.
    unfold lt; apply nat_le_dec.
  Defined.

  Lemma lt_difference: forall (p q:nat), p < q -> p <> q.
  Proof.
    induction p. intros. destruct H; discriminate. intros. destruct q. discriminate.
    apply le_S_n in H. apply IHp in H. intro. apply H. apply eq_add_S; assumption.
  Defined.
  
  Theorem difference_inequality: forall p q:nat, p <> q -> p < q \/ q < p.
  Proof.
    assert (forall p q:nat, p <= q \/ q < p) as L1.
    induction p. intros; left. apply le_0_n. intros; destruct q. right. unfold lt.
    apply le_n_S; apply le_0_n.  destruct IHp with (q:= q). left; apply le_n_S; assumption.
    right; apply le_n_S; assumption. intros; destruct L1 with (p:= p) (q:= q).
    destruct H0. apply False_ind. apply H; reflexivity. left; apply le_n_S; assumption.
    right; assumption.
  Defined.    

  Theorem no_lt_le: forall p q:nat, p <= q -> ~ q < p.
  Proof.
    intros p q i; induction i. intro. apply lt_difference in H; apply H; reflexivity.
    intro. apply IHi. apply le_S_n. apply le_S; assumption.
  Defined.

  Theorem no_double_lt: forall p q:nat, p < q -> ~q < p.
  Proof.
    intros p q i. apply no_lt_le. apply le_S_n; apply le_S; assumption.
  Defined.
    
End equalities_and_inequalities_tests.

Section elementary_permutations_of_integer_lists.

  Inductive elementary_list_permutation: list nat -> list nat -> Prop:=
  |elp_head: forall (l: list nat) (a b:nat),
      elementary_list_permutation (cons a (cons b l)) (cons b (cons a l))
  |elp_tail: forall (h:nat) (t u: list nat),
      elementary_list_permutation t u ->
      elementary_list_permutation (cons h t) (cons h u).

  (** we define the notion of permutation in n steps, with n explicit. *)
  
  Inductive list_permutation: nat -> list nat -> list nat -> Prop:=
  |lp_init: forall l:list nat, list_permutation 0 l l
  |lp_step: forall (n:nat) (p q r:list nat),
      list_permutation n p q -> elementary_list_permutation q r ->
      list_permutation (S n) p r.       
            
End elementary_permutations_of_integer_lists.

Section injectivity_of_lists.

  (** The adjective "injective" simply means here that the list doesn't feature 
   the same element twice *)
  
  Inductive nat_list_member (k:nat): list nat -> Prop:=
  |nlm_head: forall l:list nat, nat_list_member k (cons k l)
  |nlm_tail: forall (h: nat) (t: list nat),
      nat_list_member k t -> nat_list_member k (cons h t).

  Inductive injective_nat_list: list nat -> Prop:=
  |inl_nil: injective_nat_list nil
  |inl_cons: forall (h: nat) (t: list nat),
      injective_nat_list t -> ~ (nat_list_member h t) -> injective_nat_list (cons h t).  

  Lemma injectivity_head_inequality: forall (l:list nat) (a b:nat),
      injective_nat_list (cons a (cons b l)) -> a <> b.
  Proof.
    intros. intro.
    inversion H. apply H4. rewrite H0. apply nlm_head.
  Defined.
  
  Lemma injectivity_head_cases: forall (l:list nat) (a b:nat),
      injective_nat_list (cons a (cons b l)) -> (a < b \/ b < a).
  Proof.
    intros; apply difference_inequality; apply injectivity_head_inequality with (l:= l);
      assumption.
  Defined.

  Fixpoint canonical_list (n:nat) {struct n}: list nat:=
    match n with
    | 0 => nil
    | S m => cons m (canonical_list m)
    end.

  Lemma canonical_list_bound:
    forall (n p:nat), nat_list_member p (canonical_list n) -> p < n.
  Proof.
    induction n. intros p F; inversion F. simpl; intros. inversion H. apply le_n.
    apply IHn in H1. apply le_S; assumption.
  Defined.

  Theorem canonical_list_injectivity: forall n:nat, injective_nat_list (canonical_list n).
  Proof.
    induction n. simpl; apply inl_nil. simpl; apply inl_cons. assumption.
    intro F. apply canonical_list_bound in F. apply lt_difference in F. apply F; reflexivity.
  Defined.

  Lemma elementary_list_permutation_no_new_member (x: nat):
    forall p q:list nat,
      elementary_list_permutation p q -> nat_list_member x q -> nat_list_member x p.
  Proof.
    intros p q e. induction e. intros. inversion H. apply nlm_tail; apply nlm_head.
    inversion H1. apply nlm_head. repeat apply nlm_tail; assumption.
    intros. inversion H. apply nlm_head. apply nlm_tail; apply IHe; assumption.
  Defined.    
    
  Lemma injectivity_elementary_list_permutation: forall p q:list nat,
      elementary_list_permutation p q -> injective_nat_list p -> injective_nat_list q.
  Proof.
    intros p q e. induction e. intros. assert (injective_nat_list l) as L1.
    inversion H; inversion H2; assumption. apply inl_cons. apply inl_cons. assumption.
    intro F. inversion H. apply H3. apply nlm_tail; assumption. intro. inversion H0.
    apply injectivity_head_inequality in H. apply H. apply eq_sym; assumption.
    inversion H. inversion H6. apply H11; assumption. intro; apply inl_cons.
    inversion H. apply IHe; assumption. intro.
    apply elementary_list_permutation_no_new_member with (x:= h) in e. inversion H.
    contradiction. assumption.
  Defined.

  Theorem injectivity_preservation_by_permutation:
    forall (number_of_steps: nat) (p q: list nat),
      list_permutation number_of_steps p q -> injective_nat_list p -> injective_nat_list q.
  Proof.
    intros n p q e; induction e. intros; assumption. intro.
    apply injectivity_elementary_list_permutation with (p:= q). assumption.
    apply IHe; assumption.
  Defined.    
    
End injectivity_of_lists.

Section signatures_of_lists.

  Fixpoint list_signature_step (n:nat) (l:list nat) (b: bool) {struct l}: bool:=
    match l with
    | nil => b
    | cons h t => match (nat_lt_dec n h) with
                  |left _ => list_signature_step n t (negb b) 
                  |right _ => list_signature_step n t b
                  end
    end.

  Fixpoint list_signature (l:list nat) {struct l}: bool:=
    match l with
    | nil => true
    | cons h t => list_signature_step h t (list_signature t)
    end.

  Lemma elementary_list_permutation_signature_step:
    forall (n: nat) (p q: list nat),
      elementary_list_permutation p q -> forall (c: bool),
        list_signature_step n q c = list_signature_step n p c.
  Proof.
    intros n p q e. induction e. intros. simpl. destruct (nat_lt_dec n b); reflexivity.
    intros; simpl. rewrite IHe. destruct (nat_lt_dec n h). reflexivity. apply IHe.
  Defined.

  Lemma list_signature_neg: forall (n:nat) (l:list nat) (c: bool),
      list_signature_step n l (negb c) = negb (list_signature_step n l c).
  Proof.
    intro n; induction l. intros; simpl; reflexivity. intros; simpl. destruct (nat_lt_dec n a).
    rewrite IHl; reflexivity. apply IHl.
  Defined.

  Lemma double_list_signature (a b:nat): forall (l:list nat) (c: bool),
      list_signature_step a l (list_signature_step b l c) = 
      list_signature_step b l (list_signature_step a l c).
  Proof.
    induction l. intros; simpl; reflexivity. intros. simpl.
    destruct (nat_lt_dec a a0). destruct (nat_lt_dec b a0).
    repeat rewrite <- list_signature_neg; apply IHl. 
    repeat rewrite <- list_signature_neg; apply IHl.
    destruct (nat_lt_dec b a0); repeat rewrite <- list_signature_neg; apply IHl.
  Defined.

  Lemma negb_involution: forall b:bool, negb (negb b) = b.
  Proof.
    intros b; destruct b; simpl; reflexivity.
  Defined.

  (** We already reach the point where the fundamental invariant is proven, immediately below*)
  
  Theorem elementary_list_permutation_signature:
    forall (p q: list nat),
      elementary_list_permutation p q -> injective_nat_list p ->
        list_signature q = negb (list_signature p).
  Proof.
    intros p q e. induction e. intros. apply injectivity_head_cases in H. simpl.
    destruct (nat_lt_dec b a). destruct (nat_lt_dec a b).
    apply no_double_lt in l1; contradiction.
    repeat rewrite <- list_signature_neg; apply double_list_signature.
    destruct (nat_lt_dec a b).
    repeat rewrite list_signature_neg; rewrite negb_involution; apply double_list_signature.
    destruct H; contradiction. simpl. intros. rewrite IHe. rewrite <- list_signature_neg.
    apply elementary_list_permutation_signature_step; assumption.
    inversion H; assumption.
  Defined.

  Fixpoint parity_test (n:nat) {struct n}: bool :=
    match n with
    | 0 => true
    | S m => negb (parity_test m)
    end.                 

  Theorem list_permutation_signature_bool_calculation:
    forall (step_number:nat) (p q: list nat),
      list_permutation step_number p q -> injective_nat_list p ->
      list_signature q = negb (xorb (parity_test step_number) (list_signature p)).
  Proof.
    intros n p q i. induction i. simpl. destruct (list_signature l); simpl; reflexivity.
    intros. rewrite (elementary_list_permutation_signature q r). apply f_equal.
    simpl. assert (forall a b:bool, xorb (negb a) b = negb (xorb a b)) as E. intros.
    destruct a; destruct b; simpl; reflexivity. rewrite E. apply IHi; assumption.
    assumption. apply (injectivity_preservation_by_permutation n p q); assumption.
  Defined.
  
  Inductive even_number: nat -> Prop:=
  |en_0: even_number 0
  |en_p2: forall n:nat, even_number n -> even_number (S (S n)).

  Lemma even_equivalence: forall n:nat, even_number n <-> even_number (S (S n)).
  Proof.
    intros. split. apply en_p2. intro G. inversion G. assumption.
  Defined.

  Theorem parity_test_reflects_evenness: forall n:nat,
      parity_test n = true <-> even_number n.
  Proof.
    assert (forall m:nat, even_number m -> parity_test m = true) as L1.
    intros m e; induction e. intros; simpl; reflexivity.
    simpl; rewrite negb_involution; assumption.
    assert (forall n:nat, even_number n \/ even_number (S n)) as L2. induction n.
    left; apply en_0. destruct IHn. right; apply en_p2; assumption. left; assumption.
    assert (forall m:nat, parity_test m = true -> even_number m) as L3.
    induction m. intros; apply en_0. destruct m. simpl. intros. absurd (false = true).
    discriminate. assumption. intros. destruct L2 with (n:= S m). apply L1 in H0.
    simpl in H. simpl in H0. rewrite H0 in H. simpl in H. absurd (false = true).
    discriminate. assumption. assumption. intros; split. apply L3. apply L1.
  Defined.  

  (** Finally the goal of the text is below:*)
  
  Theorem list_signature_permutation_parity_invariance:
    forall (n1_step_number n2_step_number: nat)
           (p q:list nat),
      injective_nat_list p ->
      list_permutation n1_step_number p q ->
      list_permutation n2_step_number p q ->
      even_number n1_step_number <-> even_number n2_step_number.
  Proof.
    intros. apply iff_trans with (parity_test n1_step_number = true).
    apply iff_sym; apply parity_test_reflects_evenness.
    apply iff_trans with (parity_test n2_step_number = true).
    apply list_permutation_signature_bool_calculation in H0.     
    apply list_permutation_signature_bool_calculation in H1.
    rewrite H0 in H1. split. intros. rewrite H2 in H1. destruct (parity_test n2_step_number).
    reflexivity. simpl in H1. destruct (list_signature p).
    apply eq_sym; simpl in H1; assumption. simpl in H1; assumption.
    intros. rewrite H2 in H1. destruct (parity_test n1_step_number).
    reflexivity. simpl in H1. destruct (list_signature p).
    simpl in H1; assumption. apply eq_sym; simpl in H1; assumption. 
    assumption. assumption. apply parity_test_reflects_evenness.
  Defined.
  
End signatures_of_lists.

