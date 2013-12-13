signature sublistTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val sublist_curried_def : thm
    val sublist_tupled_primitive_def : thm

  (*  Theorems  *)
    val append_sublist : thm
    val append_sublist_1 : thm
    val sublist_CONS1_E : thm
    val sublist_EQNS : thm
    val sublist_NIL : thm
    val sublist_SING_MEM : thm
    val sublist_antisym : thm
    val sublist_append : thm
    val sublist_append1_E : thm
    val sublist_append_2 : thm
    val sublist_append_4 : thm
    val sublist_append_5 : thm
    val sublist_append_I : thm
    val sublist_append_both_I : thm
    val sublist_append_exists : thm
    val sublist_append_front : thm
    val sublist_cons : thm
    val sublist_cons_2 : thm
    val sublist_cons_3 : thm
    val sublist_cons_exists : thm
    val sublist_def : thm
    val sublist_equal_lengths : thm
    val sublist_every : thm
    val sublist_filter : thm
    val sublist_ind : thm
    val sublist_length : thm
    val sublist_refl : thm
    val sublist_snoc : thm
    val sublist_subset : thm
    val sublist_trans : thm

  val sublist_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "sublist"

   [sublist_curried_def]  Definition

      |- ∀x x1. sublist x x1 ⇔ sublist_tupled (x,x1)

   [sublist_tupled_primitive_def]  Definition

      |- sublist_tupled =
         WFREC
           (@R.
              WF R ∧ (∀y x l2 l1. R (l1,l2) (x::l1,y::l2)) ∧
              ∀y l2 l1 x. R (x::l1,l2) (x::l1,y::l2))
           (λsublist_tupled a.
              case a of
                ([],l1) => I T
              | (h::t,[]) => I F
              | (h::t,y::l2) =>
                  I
                    ((h = y) ∧ sublist_tupled (t,l2) ∨
                     sublist_tupled (h::t,l2)))

   [append_sublist]  Theorem

      |- ∀l1 l2 l3 l. sublist (l1 ++ l2 ++ l3) l ⇒ sublist (l1 ++ l3) l

   [append_sublist_1]  Theorem

      |- sublist (l1 ++ l2) l ⇒ sublist l1 l ∧ sublist l2 l

   [sublist_CONS1_E]  Theorem

      |- ∀l1 l2. sublist (h::l1) l2 ⇒ sublist l1 l2

   [sublist_EQNS]  Theorem

      |- (sublist [] l ⇔ T) ∧ (sublist (h::t) [] ⇔ F)

   [sublist_NIL]  Theorem

      |- sublist l1 [] ⇔ (l1 = [])

   [sublist_SING_MEM]  Theorem

      |- sublist [h] l ⇔ MEM h l

   [sublist_antisym]  Theorem

      |- sublist l1 l2 ∧ sublist l2 l1 ⇒ (l1 = l2)

   [sublist_append]  Theorem

      |- ∀l1 l1' l2 l2'.
           sublist l1 l1' ∧ sublist l2 l2' ⇒
           sublist (l1 ++ l2) (l1' ++ l2')

   [sublist_append1_E]  Theorem

      |- sublist (l1 ++ l2) l ⇒ sublist l1 l ∧ sublist l2 l

   [sublist_append_2]  Theorem

      |- ∀l1 l2 l3. sublist l1 l2 ⇒ sublist l1 (l2 ++ l3)

   [sublist_append_4]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀l l1 l2 h.
           sublist (h::l) (l1 ++ [h] ++ l2) ∧ EVERY (λx. h ≠ x) l1 ⇒
           sublist l l2

   [sublist_append_5]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀l l1 l2 h.
           sublist (h::l) (l1 ++ l2) ∧ EVERY (λx. h ≠ x) l1 ⇒
           sublist (h::l) l2

   [sublist_append_I]  Theorem

      |- ∀l1 l2. sublist l1 (l2 ++ l1)

   [sublist_append_both_I]  Theorem

      |- sublist a b ∧ sublist c d ⇒ sublist (a ++ c) (b ++ d)

   [sublist_append_exists]  Theorem

      |- ∀l1 l2 h.
           sublist (h::l1) l2 ⇒
           ∃l3 l4. (l2 = l3 ++ [h] ++ l4) ∧ sublist l1 l4

   [sublist_append_front]  Theorem

      |- ∀l1 l2. sublist l1 (l1 ++ l2)

   [sublist_cons]  Theorem

      |- ∀l1 l2 h. sublist l1 l2 ⇒ sublist l1 (h::l2)

   [sublist_cons_2]  Theorem

      |- ∀l1 l2 h. sublist (h::l1) (h::l2) ⇔ sublist l1 l2

   [sublist_cons_3]  Theorem

      |- ∀l1 l2. sublist (h::l1) l2 ⇒ sublist l1 l2

   [sublist_cons_exists]  Theorem

      |- ∀h l1 l2.
           sublist (h::l1) l2 ⇔
           ∃l2a l2b.
             (l2 = l2a ++ [h] ++ l2b) ∧ h ∉ set l2a ∧ sublist l1 l2b

   [sublist_def]  Theorem

      |- (∀l1. sublist [] l1 ⇔ T) ∧ (∀t h. sublist (h::t) [] ⇔ F) ∧
         ∀y x l2 l1.
           sublist (x::l1) (y::l2) ⇔
           (x = y) ∧ sublist l1 l2 ∨ sublist (x::l1) l2

   [sublist_equal_lengths]  Theorem

      |- ∀l1 l2. sublist l1 l2 ∧ (LENGTH l1 = LENGTH l2) ⇒ (l1 = l2)

   [sublist_every]  Theorem

      |- ∀l1 l2 P. sublist l1 l2 ∧ EVERY P l2 ⇒ EVERY P l1

   [sublist_filter]  Theorem

      |- ∀l P. sublist (FILTER P l) l

   [sublist_ind]  Theorem

      |- ∀P.
           (∀l1. P [] l1) ∧ (∀h t. P (h::t) []) ∧
           (∀x l1 y l2. P l1 l2 ∧ P (x::l1) l2 ⇒ P (x::l1) (y::l2)) ⇒
           ∀v v1. P v v1

   [sublist_length]  Theorem

      |- ∀l l'. sublist l l' ⇒ LENGTH l ≤ LENGTH l'

   [sublist_refl]  Theorem

      |- ∀l. sublist l l

   [sublist_snoc]  Theorem

      |- ∀l1 l2 h. sublist l1 l2 ⇒ sublist l1 (l2 ++ [h])

   [sublist_subset]  Theorem

      |- ∀l1 l2. sublist l1 l2 ⇒ set l1 ⊆ set l2

   [sublist_trans]  Theorem

      |- ∀l1 l2 l3. sublist l1 l2 ∧ sublist l2 l3 ⇒ sublist l1 l3


*)
end
