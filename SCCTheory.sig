signature SCCTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val SCC_def : thm
    val cond_reflexive_def : thm
    val lift_def : thm

  (*  Theorems  *)
    val SCC_loop_contradict : thm
    val TC_CASES1_RW : thm
    val TC_CASES2_RW : thm
    val scc_disjoint_lemma : thm
    val scc_lemma_1_4_1_1_2_1_3 : thm
    val scc_lemma_1_4_2_1_1_1_3_2 : thm
    val scc_lemma_1_4_2_1_1_1_3_2_1 : thm
    val scc_lemma_1_4_2_1_1_1_3_2_1_1 : thm
    val scc_lemma_1_4_2_1_1_1_3_2_2 : thm
    val scc_lemma_1_4_2_1_1_1_3_2_2_1 : thm
    val scc_lemma_x : thm
    val scc_lemma_xx : thm
    val scc_lemma_xxx : thm
    val scc_tc_inclusion : thm

  val SCC_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "SCC"

   [SCC_def]  Definition

      |- ∀R vs.
           SCC R vs ⇔
           (∀v v'. v ∈ vs ∧ v' ∈ vs ⇒ R⁺ v v' ∧ R⁺ v' v) ∧
           (∀v v'. v ∈ vs ∧ v' ∉ vs ⇒ ¬R⁺ v v' ∨ ¬R⁺ v' v) ∧
           ∃v v'. v ≠ v' ∧ v ∈ vs ∧ v' ∈ vs

   [cond_reflexive_def]  Definition

      |- ∀P R. cond_reflexive P R ⇔ ∀x. P x ⇒ R x x

   [lift_def]  Definition

      |- ∀R vs vs'. lift R vs vs' ⇔ ∃v v'. v ∈ vs ∧ v' ∈ vs' ⇒ R v v'

   [SCC_loop_contradict]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀R vs vs'.
           (lift R)⁺ vs vs' ∧ (lift R)⁺ vs' vs ⇒ ¬SCC R vs ∧ ¬SCC R vs'

   [TC_CASES1_RW]  Theorem

      |- ∀R x z. R x z ∨ (∃y. R x y ∧ R⁺ y z) ⇔ R⁺ x z

   [TC_CASES2_RW]  Theorem

      |- ∀R x z. R x z ∨ (∃y. R⁺ x y ∧ R y z) ⇔ R⁺ x z

   [scc_disjoint_lemma]  Theorem

      |- ∀R vs vs'. SCC R vs ∧ SCC R vs' ∧ vs ≠ vs' ⇒ DISJOINT vs vs'

   [scc_lemma_1_4_1_1_2_1_3]  Theorem

      |- ∀R R' P.
           (∀x y.
              P x ∧ P y ⇒
              (R x y ⇒ R' x y) ∧ (λx y. R x y ∧ P x ∧ P y)⁺ x y) ⇒
           ∀x y. P x ∧ P y ⇒ R'⁺ x y

   [scc_lemma_1_4_2_1_1_1_3_2]  Theorem

      |- ∀R R' P x y.
           reflexive R' ∧ (∀x y. P x ∧ P y ⇒ R' x y ⇒ R x y) ∧ ¬R⁺ x y ⇒
           ¬R'⁺ x y ∨ ∃z. ¬P z ∧ R'⁺ x z ∧ R'⁺ z y

   [scc_lemma_1_4_2_1_1_1_3_2_1]  Theorem

      |- ∀R R' P x y.
           (∀x y. P x y ⇒ R' x y ⇒ R x y) ∧ ¬R⁺ x y ⇒
           ¬(λx y. R' x y ∧ P x y)⁺ x y

   [scc_lemma_1_4_2_1_1_1_3_2_1_1]  Theorem

      |- ∀R P x y. ¬R⁺ x y ⇒ ¬(λx y. R x y ∧ P x y)⁺ x y

   [scc_lemma_1_4_2_1_1_1_3_2_2]  Theorem

      |- ∀R'.
           reflexive R' ⇒
           ∀P x y.
             R'⁺ x y ⇒
             (λx y. R' x y ∧ P x ∧ P y)⁺ x y ∨ ∃z. ¬P z ∧ R'⁺ x z ∧ R'⁺ z y

   [scc_lemma_1_4_2_1_1_1_3_2_2_1]  Theorem

      |- ∀R P x y. (λx y. R x y ∧ P x y)⁺ x y ⇒ R⁺ x y

   [scc_lemma_x]  Theorem

      |- ∀R x z. R x z ∨ (∃y. R x y ∧ R⁺ y z) ⇒ R⁺ x z

   [scc_lemma_xx]  Theorem

      |- ∀R R' P P'.
           (∀x y.
              P x ∧ P' y ⇒
              (R x y ⇒ R' x y) ∧ (λx y. R x y ∧ P x ∧ P' y)⁺ x y) ⇒
           ∀x y. P x ∧ P' y ⇒ R'⁺ x y

   [scc_lemma_xxx]  Theorem

      |- ∀R x z. R x z ∨ (∃y. R⁺ x y ∧ R y z) ⇒ R⁺ x z

   [scc_tc_inclusion]  Theorem

      |- ∀R vs v v'.
           v ∈ vs ∧ v' ∈ vs ∧ SCC R vs ∧ reflexive R ⇒
           (λv v'. R v v' ∧ v ∈ vs ∧ v' ∈ vs)⁺ v v'


*)
end
