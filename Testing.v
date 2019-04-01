Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Ascii.
Require Import StringSplit.
Require Import CCG.
Require Import Specs.
Require Import Dictionary.


Set Typeclasses Unique Instances.


Definition addone (n:nat) := n + 1.
Polymorphic Instance addonelexicon : lexicon "addone" NP := { denotation := addone }.

Polymorphic Lemma mid2 : spec "addone is monotone".
  compute [spec sdenote denotation Reassoc SynthLex SynthLApp SynthRApp monotone_adj noun_is_adj_sentence onelexicon addslexicon foolexicon _injlexicon bridgeStringWords denote addonelexicon].
  unfold addone.
  eauto with arith.
Qed.

Polymorphic Goal Split "addone equals addone" ([fromStr "addone"] ++ [fromStr "equals"] ++ [fromStr "addone"]).
  typeclasses eauto.
Qed.
Polymorphic Goal Synth ([fromStr "addone"] ++ [fromStr "equals"] ++ [fromStr "addone"]) S.
  typeclasses eauto.
Qed.
Polymorphic Goal Semantics "addone equals addone" S.
  typeclasses eauto.
Qed.
Polymorphic Goal spec "addone equals addone".
  reflexivity.
Qed.

Polymorphic Lemma sem : Semantics "addone given 3" (@NP nat).
  typeclasses eauto.
Qed.
Print sem.

Goal spec "addone given 3 equals 4".
  reflexivity.
Qed.
(** Earlier we used 'is' taking a noun and adjective, here we use a different meaning of 'is' disambiguated by its grammatical position. *)
Goal spec "addone given 3 is 4".
  reflexivity.
Qed.
(** We can even prove their denotations are equal (not just logically equivalent) to double-check the English understanding: *)
Goal spec "addone given 3 is 4" = spec "addone given 3 equals 4".
  reflexivity.
Qed.
(** Logical equivalence is possible too, but less meaningful since both sides are tautologies. *)


Goal spec "addone is monotone".
Proof.
  compute.
  eauto with arith.
Qed.
Goal spec "addone given 3 is 4".
  reflexivity.
Qed.







Polymorphic Goal Semantics "every natural is nonneg" S.
eapply @bridgeStringWords.
typeclasses eauto.

eapply @Reassoc.
eapply @SynthRApp.
- eapply @SynthRApp.

  eapply @SynthLex. eapply (@forall_lex nat).

  eapply @SynthLex. eapply @nat_noun. 

- eapply @SynthRApp. eapply @SynthShift. eapply SynthLex.
  eapply noun_is_adj_sentence.
  eapply SynthLex. eapply nonneg.
Qed.

Polymorphic Goal spec "every natural is nonneg".
simpl.
eauto with arith.
Qed.

Polymorphic Goal spec "some natural is nonneg".
simpl.
exists 5. eauto with arith.
Qed.


Ltac justparse :=
  eapply @bridgeStringWords;
  match goal with [ |- Split _ _ ] => typeclasses eauto | _ => idtac end.

Typeclasses eauto := (dfs) 15.
Polymorphic Goal spec "4 is even and nonneg".
Proof.
  simpl. split. eauto with arith. eauto with arith.
Qed.


Polymorphic Goal Semantics "3 is nonneg and 4 is even" S.
Proof.
  justparse.
  eapply Reassoc. eapply Reassoc.
  eapply SynthLApp.
  2: { eapply SynthRApp. typeclasses eauto. typeclasses eauto. }
  eapply SynthRApp. eapply SynthLApp. typeclasses eauto.
  eapply SynthLex. eapply noun_is_adj_sentence.
  typeclasses eauto.
Qed.
Goal spec "3 is nonneg and 4 is even".
split; simpl; eauto with arith.
Qed.



Ltac dictionary :=
  eapply SynthLex; typeclasses eauto.
Polymorphic Lemma x : Semantics "every natural is nonneg and some natural is even" S.
Proof.
  justparse.
  eapply Reassoc. eapply Reassoc. eapply Reassoc.
  eapply SynthLApp.

  { (* every : ((S // ((@NP A) \\ S) // (@CN A)))
       every natural : S // ((@NP A) \\ S)
       is : (@NP A \\ (S // @ADJ A))
       even : @ADJ A
       w/ reassoc, is : (@NP A \\ S) // @ADJ A
      then composition should fix things. *)
    eapply SynthRApp; try dictionary.

    eapply RComp. eapply SynthRApp. dictionary. dictionary.
    eapply SynthShift. dictionary. }

    eapply SynthRApp. eapply SynthShift; dictionary.
    eapply Reassoc. eapply SynthRApp.
    eapply SynthRApp; dictionary.
    eapply SynthRApp; try dictionary.
    eapply SynthShift. dictionary.
Qed.
Print x.

Polymorphic Goal Semantics "3 is even" S.
typeclasses eauto.
Qed.

Polymorphic Goal Synth ([fromStr "every"] ++ [fromStr "natural"] ++ [fromStr "is"] ++ [fromStr "nonneg"] ++ [fromStr "and"] ++ [fromStr "some"] ++ [fromStr "natural"] ++ [fromStr "is"] ++ [fromStr "even"]) S.
Proof.
typeclasses eauto.
Qed.
(** These take a long time to process.... Bounding the search depth helps.*)
Typeclasses eauto := (dfs) 15.

Polymorphic Goal Semantics "every natural is nonneg and some natural is even" S.
typeclasses eauto.
Qed.

Polymorphic Lemma certificate_example : Semantics "4 is even" S.
Proof.
  typeclasses eauto.
Qed.
Print certificate_example.

Polymorphic Goal Semantics "every natural is odd or even" S.
justparse.
eapply Reassoc. eapply SynthRApp. eapply SynthRApp. dictionary. dictionary.
eapply SynthRApp. eapply SynthShift. eapply SynthLex. eapply noun_is_adj_sentence.
Check or_adj.
eapply SynthLApp; try dictionary. eapply SynthRApp. dictionary. dictionary.
Qed.
Goal spec "every natural is odd or even".
Abort.
