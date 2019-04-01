Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Ascii.
Require Import StringSplit.
Require Import CCG.
(*Set Typeclasses Unique Instances.*)
Polymorphic Definition wordSpec (l : list word){parse : Synth l S} : Prop := @denote l S parse.

Polymorphic Class StringParse (s : string){ws}{parse : Synth ws S} := { strdenote : Prop }.
Polymorphic Instance doStringParse (s:string)(ws:list word){split : Split s ws}{parse : Synth ws S} : StringParse s :=
  { strdenote := @denote ws S parse }.
Polymorphic Class Parsed (s:string) := { splitstring : list word }.
Polymorphic Instance doParse (s:string){ws:list word}{split : Split s ws} : Parsed s := { splitstring := ws }.

Polymorphic Class Semantics (s : string) (cat : GType) := { sdenote : interp cat }.
Polymorphic Instance bridgeStringWords {s ws cat}(sw:Split s ws)(parse:Synth ws cat) : Semantics s cat :=
  { sdenote := @denote _ _ parse }.

Polymorphic Definition spec (s : string)`{sem : Semantics s S} := @sdenote _ _ sem .
