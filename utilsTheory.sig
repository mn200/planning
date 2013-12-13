signature utilsTheory =
sig
  type thm = Thm.thm

  (*  Theorems  *)
    val twosorted_list_length : thm

  val utils_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "utils"

   [twosorted_list_length]  Theorem

      |- ∀P1 P2 l k1 k2.
           (∀x. MEM x l ⇒ (¬P1 x ⇔ P2 x)) ∧ LENGTH (FILTER P1 l) < k1 ∧
           (∀l'.
              (∃pfx sfx. pfx ++ l' ++ sfx = l) ∧ (∀x. MEM x l' ⇒ P2 x) ⇒
              LENGTH l' < k2) ⇒
           LENGTH l < k1 * k2


*)
end
