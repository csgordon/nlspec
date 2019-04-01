Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Ascii.
Require Import StringSplit.
Require Import CCG.

Polymorphic Instance onelexicon : lexicon (fromStr "one") NP := { denotation := 1 }.
(* This adds denotation isn't right, since it really should be taking the subj as a function *)
Polymorphic Instance addslexicon : lexicon ("adds") (NP \\ (S // NP)) := {
 denotation := fun subj dirobj => forall (x:nat), subj x = x + dirobj }.
Polymorphic Instance foolexicon : lexicon "foo" NP := { denotation := 0 }.

Polymorphic Instance monotone_adj : lexicon "monotone" ADJ := { denotation f := forall (x y:nat), x <= y -> f x <= f y }.
Polymorphic Instance noun_is_adj_sentence {A:Type} : lexicon "is" (@NP A \\ (S // @ADJ A)) := { denotation n a := a n }.
Polymorphic Instance noun_is_noun_sentence {A:Type} : lexicon "is" (@NP A \\ (S // @NP A)) := { denotation n a := n = a }.

Polymorphic Instance equalslex (A:Type) : lexicon "equals" ((@NP A \\ S) // @NP A) := { denotation x y := x = y }.

Polymorphic Instance fourlex : lexicon "4" NP := {denotation := 4}.
Polymorphic Instance threelex : lexicon "3" NP := {denotation := 3}.
Polymorphic Instance givenlex (A B:Type) : lexicon "given" ((@NP (A -> B)) \\ (@NP B // @NP A)) :=
  { denotation f arg := f arg }.

(** Relation vocabulary *)
Require Import Coq.Relations.Relations.
Polymorphic Instance reflexive_vocab (A:Type) : lexicon "reflexive" (@ADJ (relation A)) :=
  { denotation r := reflexive _ r }.
Polymorphic Instance transitive_vocab (A:Type) : lexicon "transitive" (@ADJ (relation A)) := { denotation r := transitive _ r}.
Polymorphic Instance symmetric_vocab (A:Type) : lexicon "symmetric" (@ADJ (relation A)) := { denotation r := symmetric _ r}.
Polymorphic Instance antisymmetric_vocab (A:Type) : lexicon "antisymmetric" (@ADJ (relation A)) := { denotation r := antisymmetric _ r}.

Polymorphic Instance preorder_vocab (A:Type) : lexicon "preorder" (@ADJ (relation A)) :=
  { denotation r := preorder _ r }.
Polymorphic Instance order_vocab (A:Type) : lexicon "order" (@ADJ (relation A)) :=
  { denotation r := order _ r }.

Require Import Coq.Arith.Even.

Polymorphic Instance even_lex : lexicon "even" ADJ := { denotation := even }.
Polymorphic Instance and_adj {A:Type} : lexicon "and" (@ADJ A \\ (@ADJ A) // @ADJ A) := {
  denotation := fun l r => fun x => (l x /\ r x)
}.
Polymorphic Instance and_sent : lexicon "and" (S \\ (S // S)) := {
  denotation := fun l r => l /\ r
}.
Polymorphic Instance or_adj {A:Type} : lexicon "or" (@ADJ A \\ (@ADJ A) // @ADJ A) := {
  denotation := fun l r => fun x => (l x \/ r x)
}.
Polymorphic Instance or_sent : lexicon "or" (S \\ (S // S)) := {
  denotation := fun l r => l \/ r
}.

Polymorphic Instance exists_lex {A:Type} 
: lexicon "some" (Quant A) (*(S // ((@NP A) \\ S)) // (@CN A)*) := {
  denotation := fun _ P => (exists (x:A), P x)
}.
Polymorphic Instance forall_lex {A:Type} 
: lexicon "every" (Quant A) (*(S // ((@NP A) \\ S)) // (@CN A)*) := {
  denotation := fun _ P => (forall (x:A), P x)
}.

Polymorphic Instance and_liftL {G G'} (nxt:lexicon "and" (G \\ G // G)) :
  lexicon "and" ((G' \\ G) \\ (G' \\ G) // (G' \\ G)) :=
{ denotation := fun R L g' => denotation (R g') (L g') }. 
Polymorphic Instance or_liftL {G G'} (nxt:lexicon "or" (G \\ G // G)) :
  lexicon "or" ((G' \\ G) \\ (G' \\ G) // (G' \\ G)) :=
{ denotation := fun R L g' => denotation (R g') (L g') }. 
Polymorphic Instance and_liftR {G G'} (nxt:lexicon "and" (G' \\ G' // G')) :
  lexicon "and" ((G' // G) \\ (G' // G) // (G' // G)) :=
{ denotation := fun R L g' => denotation (R g') (L g') }. 
Polymorphic Instance or_liftR {G G'} (nxt:lexicon "or" (G' \\ G' // G')) :
  lexicon "or" ((G' // G) \\ (G' // G) // (G' // G)) :=
{ denotation := fun R L g' => denotation (R g') (L g') }. 

(* currently, don't have split instances up to "non-negative" length *)
Polymorphic Instance nonneg : lexicon "nonneg" (ADJ) := { denotation := (fun x => x >= 0) }.
Print lexicon.
Polymorphic Definition def_adj {T:Type} (s:string) (p:T->Prop) : lexicon s ADJ := 
  Build_lexicon s ADJ p.
Polymorphic Definition def_noun {T:Type} (s:string) (x:T) : lexicon s (@NP T) :=
  Build_lexicon s NP x.
Polymorphic Instance pos_lex: lexicon "odd" ADJ := def_adj "odd" odd.
Polymorphic Instance plus_lex: lexicon _ _ := def_noun "plus" plus.


Notation "'denote_type' X" := (@exist Type (fun T => T = X) X eq_refl) (at level 65).

Polymorphic Instance nat_noun : lexicon "natural" (@CN nat) := {
  denotation := denote_type nat (*@exist Type (fun T => T = nat) nat eq_refl*)
}.
