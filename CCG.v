Require Import Coq.Lists.List.
Import ListNotations.
Require Import StringSplit.

Polymorphic Inductive GType : Type :=
| S
| NP : forall {x:Type}, GType
| rSlash : GType -> GType -> GType
| lSlash : GType -> GType -> GType
| ADJ : forall {x:Type}, GType
| CN : forall {A:Type}, GType
.
Notation "a // b" := (rSlash a b) (at level 60).
Notation "a \\ b" := (lSlash a b) (at level 60).
Notation "'Quant' A" := ((S // ((@NP A) \\ S)) // (@CN A)) (at level 45).
Polymorphic Fixpoint interp (c : GType) : Type :=
match c with 
| S => Prop
| @NP t => t (* This shows the need for indexing by referent --- maybe just for NP, and for S? Not sure how slashes would interact, since traditional logical form is set-based. *)
| rSlash a b => interp b -> interp a
| lSlash a b => interp a -> interp b
| @ADJ t => t -> Prop
| @CN t => { T : Type | T = t }
end.
Notation "'Quant' A" := ((S // ((@NP A) \\ S) // (@CN A))) (at level 45).

Polymorphic Class lexicon (w : word) (cat : GType) := {
  denotation : interp cat
}.

Polymorphic Instance _injlexicon {T:Type}{t:T}: lexicon (_inj T t) (@NP T) := { denotation := t }.
Notation "& x" := (_inj _ x) (at level 55).

Polymorphic Class Synth (l : list word) (cat : GType) := {
  denote : interp cat
}.
Polymorphic Instance SynthLex {w cat}`(lexicon w cat) : Synth [w] cat := { denote := denotation}.

(** * AB Categorial Rules *)
(** ** Forward Application *)
Polymorphic Instance SynthRApp {s1 s2 c1 c2}(L:Synth s1 (c1 // c2))
                                    (R:Synth s2 c2) :
                                      Synth (app s1 s2) c1 := {
  denote := @denote s1 (c1 // c2) L (@denote s2 c2 R)
}.
(** ** Backward Application *)
Polymorphic Instance SynthLApp {s1 s2 c1 c2}(L:Synth s1 c1)
                                    (R:Synth s2 (c1 \\ c2)) :
                                      Synth (app s1 s2) c2 := {
  denote := @denote s2 (c1 \\ c2) R (@denote s1 c1 L)
                                                                 }.
(** Associativity --- only this direction is required, because we use this in a setup where
     all inputs are already associated all the way to the right. *)
Polymorphic Instance Reassoc {s1 s2 s3 c}(pre:Synth ((s1 ++ s2) ++ s3) c) : Synth (s1 ++ (s2 ++ s3)) c := {
  denote := @denote _ _ pre
}.

(** Shift reassociates the nesting of opposing slash types. Again, by normalizing our lexicon's types, we can get away with only this direction. *)
Polymorphic Instance SynthShift {s c l r}(L:Synth s (l \\ (c // r)))  :
                                      Synth s ((l \\ c) // r) := {
  denote := fun xr xl => @denote _ _ L xl xr
}.
(** >B and <B Composition --- Normally derived from hypotheticals *)
Polymorphic Instance RComp {s s' c1 c2 c3}(L:Synth s (c1 // c2))(R:Synth s' (c2 // c3))
  : Synth (s ++ s') (c1 // c3) := {
  denote := fun x3 => @denote _ _ L (@denote _ _ R x3)
}.
Polymorphic Instance LComp {s s' c1 c2 c3}(L:Synth s (c1 \\ c2))(R:Synth s' (c2 \\ c3))
  : Synth (s ++ s') (c1 \\ c3) := {
  denote := fun x1 => @denote _ _ R (@denote _ _ L x1)
}.


