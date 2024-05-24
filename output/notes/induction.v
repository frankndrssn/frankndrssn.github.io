Require Import Lia.
(** * Mathematical induction *)
Section Induction.

(** Every inductive type admits an induction principle (elimination principle).
 Coq automatically generates an induction principle whenever an inductive type
 is defined. *)
Print nat.
Check nat_ind.
(* [nat_ind :
      forall P : nat -> Prop,
      P 0 ->
      (forall n : nat, P n -> P (S n)) ->
      forall n : nat, P n] *)

(** We can use the induction principle to define various operations on [nat],
    e.g., addition. Here, we need to use [nat_rec] for a technical reason
    that's not important for now. *)
Definition add_ind : nat -> nat -> nat :=
  nat_rec
    (fun n => nat -> nat)
    (fun x => x)
    (fun _ f x => S (f x)).

(** [add_ind] looks like magic. It's difficult to use the induction principle
    directly, so Coq allows definition by _pattern matching_. *)
Print "+".
(* [Nat.add = 
      fix add (n m : nat) {struct n} : nat :=
      match n with
      | 0 => m
      | S p => S (add p m)
      end
      : nat -> nat -> nat] *)

(** These two functions are equivalent in terms of what they compute. We can use
    induction to prove this fact. To use induction, we need to supply a
    _motive_ [P]. Here, [P n := forall m, add_ind n m = n + m] is a reasonable
    choice. *)
Theorem add_ind_eqv_add :
  forall n m, add_ind n m = n + m.
Proof.
  set (P := fun n => forall m, add_ind n m = n + m).
  apply (nat_ind P); unfold P.
  - easy.
  - intros n IHn m.
    simpl.
    now rewrite IHn.
Qed.

(** We can also choose [P n := add_ind n m = n + m] if [m] is already in the
    context. *)
Theorem add_ind_eqv_add' :
  forall n m, add_ind n m = n + m.
Proof.
  intros n m.
  set (P := fun n => add_ind n m = n + m).
  apply (nat_ind P); unfold P.
  - easy.
  - intros n' IHn'.
    simpl.
    now destruct IHn'.
Qed.

(** Note that the induction hypothesis in [add_ind_eqv_add'] is
    [add_ind n' m = n' + m], which is weaker than the induction hypothesis in
    [add_ind_eqv_add] ([forall m : nat, add_ind n m = n + m]). The proof goes through
    because we do not need the extra generality on [m] in this case, but
    sometimes the extra generality is the key to proving the given theorem. *)

(** Coq has the [induction] tactic that automatically finds a motive for us. It
    also does a number of boring steps such as [intros] for us. Compare the
    induction hypotheses in the following two proofs. *)
Theorem add_ind_eqv_add_tactic :
  forall n m, add_ind n m = n + m.
Proof.
  induction n.
  - easy.
  - intros m.
    simpl.
    now rewrite IHn.
Qed.

Theorem add_ind_eqv_add_tactic' :
  forall n m, add_ind n m = n + m.
Proof.
  intros n m.
  induction n.
  - easy.
  - simpl.
    now destruct IHn.
Qed.

(** Thus, we must be conscious of what we [intros] into the context before
    [induction]. *)

(** The successor [S] is equivalent to adding 1. *)
Theorem succ_add_1 :
  forall n, S n = 1 + n.
Proof.
  easy.
Qed.

(** This simple proof does not work when we state the theorem slightly
    differently. *)
Theorem succ_add_1' :
  forall n, S n = n + 1.
Proof.
  intros n.
  try reflexivity.
Abort.

(** The reason is that [+] is recursive on the first argument. [n + 1] is
    stuck because we have no computation rules to handle [n], whereas [1 + n]
    is [(S 0) + n] and we know how to compute this term: this computes to
    [S (0 + n)], which then computes to [S n]. But, we know that [n] must be
    either [0] or [S n'] for some [n'] because [nat] is inductively defined by
    these two constructors. We can use induction to do this kind of case
    analysis. Sometimes the induction hypothesis is not useful. We can use
    [destruct] instead of [induction] in those cases. *)
Theorem succ_add_1' :
  forall n, S n = n + 1.
Proof.
  induction n.
  - easy.
  - simpl.
    now destruct IHn.
Qed.

(** We can now prove various facts about addition. *)

(** [add_comm] is an example of why we need to be conscious of what we [intros]
    into the context. Consider the following attempt. *)

(** Addition is commutative. *)
Theorem add_comm :
  forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - induction m.
    + easy.
    + simpl.
      now destruct IHm.
  - induction m.
    + simpl.
      now rewrite IHn.
    + simpl.
      admit.
Abort.

(** Just before the second [induction m], the context contains a hypothesis
    [IHn : n + m = m + n]. Since [m] appears free in this hypothesis, the
    [induction] tactic has to generate the motive
    [P m := n + m = m + n -> S n + m = m + S n]. So, the induction hypothesis is
    [n + m = m + n -> S n + m = m + S n]. *)

(** To rewrite with [IHm], we need to prove [n + m = m + n], so we are stuck. *)

(** But the proof goes through if we do not [intros m] in the beginning. *)
Theorem add_comm :
  forall n m, n + m = m + n.
Proof.
  induction n.
  - induction m.
    + easy.
    + simpl.
      now destruct IHm.
  - induction m.
    + simpl.
      now rewrite IHn.
    + simpl.
      destruct IHm.
      rewrite IHn.
      simpl.
      now rewrite IHn.
Qed.

(** In the proof above, the context just before the second [induction m]
    contains [IHn : forall m, n + m = m + n]. Since [m] does not appear free in this
    hypothesis, [induction] can generate the motive
    [P m := S n + m = m + S n]. *)

(** Addition is associative. *)
Theorem add_assoc :
  forall a b c, (a + b) + c = a + (b + c).
Proof.
  intros a b c.
  induction a.
  - easy.
  - simpl.
    now destruct IHa.
Qed.

(** * Lists and their induction principle *)
(** For simplicity, let us consider lists of [nat]s. *)
Inductive nat_list : Set :=
| nil : nat_list
| cons : nat -> nat_list -> nat_list.

(** Lists are inductively constructed by two constructors: [nil] and [cons].
    So, to eliminate out of a list, it suffices to specify an action on [nil]
    and an action on [cons n l]. *)
Check nat_list_ind.
(* [nat_list_ind
     : forall P : nat_list -> Prop,
       P nil ->
       (forall (n : nat) (n0 : nat_list), P n0 -> P (cons n n0)) ->
       forall n : nat_list, P n] *)

(** We can define operations on [nat_list] by recursion. *)

(** [length l] is the length of [l]. *)
Fixpoint length (l : nat_list) : nat :=
  match l with
  | nil => 0
  | cons _ l => S (length l)
  end.

(** [concate l s] is the concatenation of [l] and [s]. *)
Fixpoint concate (l s : nat_list) : nat_list :=
  match l with
  | nil => s
  | cons a l => cons a (concate l s)
  end.

(** [reverse l] is the reversal of [l]. *)
Fixpoint reverse (l : nat_list) : nat_list :=
  match l with
  | nil => nil
  | cons a l => concate (reverse l) (cons a nil)
  end.

(** [length] commutes with [concate] with respect to [+]. *)
Theorem length_comm_concate :
  forall l s, length (concate l s) = length l + length s.
Proof.
  intros l s.
  induction l.
  - reflexivity.
  - simpl.
    now destruct IHl.
Qed.

(** [reverse] preserves [length]. *)
Theorem reverse_pre_length :
  forall l, length (reverse l) = length l.
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite length_comm_concate.
    destruct IHl.
    simpl.
    lia.
Qed.

(** [nil] is the right identity w.r.t. [concate]. *)
Theorem concate_nil :
  forall l, concate l nil = l.
Proof.
  induction l.
  - easy.
  - simpl.
    now rewrite IHl.
Qed.

(** [reverse] is identity on singletons. *)
Theorem reverse_id_singleton :
  forall n, reverse (cons n nil) = cons n nil.
Proof.
  easy.
Qed.

(** [concate] is associative. *)
Theorem concate_assoc :
  forall l s t, concate (concate l s) t = concate l (concate s t).
Proof.
  intros l s t.
  induction l.
  - easy.
  - simpl.
    now destruct IHl.
Qed.

(** [reverse] commutes with [concate]. *)
Theorem reverse_comm_concate :
  forall l s, reverse (concate l s) = concate (reverse s) (reverse l).
Proof.
  intros l s.
  induction l.
  - simpl.
    now rewrite concate_nil.
  - simpl.
    rewrite IHl.
    apply concate_assoc.
Qed.

(** [reverse] is involutative. *)
Theorem reverse_invol :
  forall l, reverse (reverse l) = l.
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite reverse_comm_concate.
    now rewrite IHl.
Qed.

(** [reverse] is injective. *)
Theorem reverse_inj :
  forall l s, reverse l = reverse s -> l = s.
Proof.
  intros l s eq.
  assert (eq' : reverse (reverse l) = reverse (reverse s)). {
    now destruct eq.
  }
  repeat rewrite reverse_invol in eq'.
  easy.
Qed.

(** [concate] is injective in the second argument. *)
Theorem concate_inj_second :
  forall l s1 s2, concate l s1 = concate l s2 -> s1 = s2.
Proof.
  intros l s1 s2.
  induction l; simpl in *; intros eq.
  - easy.
  - inversion eq; subst.
    now apply IHl.
Qed.

(** [concate] is also injective in the first argument. This is a corollary of
    [concate_inj_second]. *)
Theorem concate_inj_first :
  forall l1 l2 s, concate l1 s = concate l2 s -> l1 = l2.
Proof.
  intros l1 l2 s eq.
  assert (eq' : reverse (concate l1 s) = reverse (concate l2 s)). {
    now rewrite eq.
  }
  clear eq.
  repeat rewrite reverse_comm_concate in eq'.
  apply concate_inj_second in eq'.
  apply reverse_inj.
  easy.
Qed.

(** A list is said to be a _palindrome_ if it equals its own reversal. *)
Definition palindrome (l : nat_list) : Prop := l = reverse l.

(** The empty list is a palindrome. *)
Example palindrome_nil : palindrome nil.
Proof.
  easy.
Qed.

(** Singleton lists are palindromes. *)
Example palindrome_single :
  forall n, palindrome (cons n nil).
Proof.
  easy.
Qed.

(** We can equivalently express [palindrome] as an inductively defined relation.
    Each constructor specifies a canonical proof of this relation. *)
Inductive palindrome' : nat_list -> Prop :=
| pal_nil : palindrome' nil
| pal_single : forall n, palindrome' (cons n nil)
| pal_more : forall n l, palindrome' l ->
                    palindrome' (cons n (concate l (cons n nil))).

(** [palindrome'] is sound. The proof is a simple induction on the derivation of
    [palindrome' l]. *)
Theorem palindrome'_sound :
  forall l, palindrome' l -> palindrome l.
Proof.
  intros l pal.
  induction pal.
  - apply palindrome_nil.
  - apply palindrome_single.
  - unfold palindrome in *.
    simpl.
    rewrite reverse_comm_concate.
    rewrite <- IHpal.
    now rewrite reverse_id_singleton.
Qed.

(** This technical lemma allows us to extract the middle part of a
    palindrome. *)
Lemma palindrome_inversion :
  forall n l, palindrome (cons n l) ->
         l <> nil ->
         exists l', l = reverse (cons n l').
Proof.
  intros n l pal neq; unfold palindrome in pal.
  destruct (reverse l) eqn:eq.
  - exfalso.
    apply neq.
    rewrite <- (reverse_invol l).
    now rewrite eq.
  - clear neq.
    rename n1 into l1.
    simpl in pal.
    rewrite eq in pal.
    simpl in pal.
    inversion pal; subst.
    clear pal.
    simpl.
    exists (reverse l1).
    now rewrite reverse_invol.
Qed.

(** Completeness is a lot harder to prove. A straightforward induction on [l]
    (or [length l]) fails. An intuitive explanation is that, to use [pal_more],
    we need to look at a list with 2 less elements, but the induction hypothesis
    is not strong enough to accomplish this. *)

(** To resolve this issue, we can introduce a "fuel" variable and show that
    [palindrome'] is complete for any amount of fuel. *)
Lemma palindrome'_complete_fuel :
  forall m l, length l < m -> palindrome l -> palindrome' l.
Proof.
  induction m; intros l lt pal.
  - destruct l; inversion lt.
  - destruct l; [| destruct l].
    + constructor.
    + constructor.
    + apply palindrome_inversion in pal as h; try discriminate.
      destruct h as [l' eq].
      unfold palindrome in pal.
      symmetry in eq.
      destruct eq.
      simpl in pal.
      rewrite <- reverse_id_singleton in pal.
      rewrite reverse_comm_concate in pal.
      rewrite reverse_invol in pal.
      simpl in pal.
      inversion pal as [eq]; subst.
      apply concate_inj_first in eq.
      simpl.
      constructor.
      apply IHm.
      * rewrite reverse_pre_length.
        simpl in lt.
        rewrite length_comm_concate in lt.
        rewrite reverse_pre_length in lt.
        lia.
      * easy.
Qed.
        
(** Now, completeness is an immediate corollary of
    [palindrome'_complete_fuel]. *)
Theorem palindrome'_complete :
  forall l, palindrome l -> palindrome' l.
Proof.
  intros l pal.
  apply palindrome'_complete_fuel with (m := S (length l)).
  - constructor.
  - easy.
Qed.

(** * Well-founded induction *)

(** We can generalize the "fuel" technique. An inhabitant [x] is said to be
    _accessible_ (w.r.t. a relation [R]) if for all [y] with [y R x], [y] is
    accessible. *)
Inductive acc {A : Type} {R : A -> A -> Prop} : A -> Prop :=
| acc_k : forall x, (forall y, R y x -> acc y) -> acc x.


(** A relation is said to be _well-founded_ if every inhabitant is
    accessible. *)
Definition wf {A : Type} (R : A -> A -> Prop) : Prop :=
  forall x, @acc A R x.

(** We can now define well-founded induction. *)
Definition wf_ind :
  forall {A : Type} {R : A -> A -> Prop} (P : A -> Prop),
    wf R ->
    (forall x, (forall y, R y x -> P y) -> P x) ->
    forall x, P x.
Proof.
  refine (fun A R P wf f x => _).
  refine (acc_ind A R _ _ _ (wf x)).
  refine (fun _ _ g => f _ _).
  refine (fun y r => g _ r).
Defined.

(** [<] is well-founded. *)
Theorem wf_lt : wf lt.
Proof.
  unfold wf.
  induction x.
  - constructor.
    intros y lt.
    inversion lt.
  - induction IHx.
    constructor.
    intros y lt.
    constructor.
    intros y2 lt2.
    constructor.
    intros y3 lt3.
    apply H.
    lia.
Qed.

(** Strong induction is a special case of [wf_ind]. *)
Definition strong_ind :
  forall (P : nat -> Prop),
    (forall x, (forall y, y < x -> P y) -> P x) ->
    forall x, P x.
Proof.
  exact (fun P => @wf_ind nat lt P wf_lt).
Defined.

(** We can define a well-founded relation on lists. *)
Definition R (l l' : nat_list) : Prop := length l < length l'.

Theorem wf_R : wf R.
Proof.
  unfold wf.
  induction x.
  - constructor.
    intros y r.
    inversion r.
  - induction IHx.
    constructor.
    intros y r.
    constructor.
    intros y0 r0.
    apply H.
    unfold R in *.
    simpl in r.
    lia.
Qed.

(** We can now do strong induction on lists. *)
Definition strong_list_ind :
  forall (P : nat_list -> Prop),
    (forall x, (forall y, R y x -> P y) -> P x) ->
    forall x, P x.
Proof.
  exact (fun P => @wf_ind nat_list R P wf_R).
Defined.

(** We can use [strong_list_ind] to prove [palindrome'_complete]. The proof is
    essentially the same. *)
Theorem palindrome'_complete_strong :
  forall l, palindrome l -> palindrome' l.
Proof.
  induction l as [l f] using strong_list_ind.
  intros pal.
  destruct l; [| destruct l].
  - constructor.
  - constructor.
  - apply palindrome_inversion in pal as h; try discriminate.
    destruct h as [l' eq].
    unfold palindrome in pal.
    symmetry in eq.
    destruct eq.
    simpl in pal.
    rewrite <- reverse_id_singleton in pal.
    rewrite reverse_comm_concate in pal.
    rewrite reverse_invol in pal.
    simpl in pal.
    inversion pal as [eq]; subst.
    apply concate_inj_first in eq.
    simpl.
    constructor.
    apply f.
    * unfold R.
      simpl.
      rewrite length_comm_concate.
      simpl.
      repeat rewrite reverse_pre_length.
      lia.
    * easy.
Qed.

End Induction.
