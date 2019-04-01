Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Ascii.
(*Set Typeclasses Unique Instances.*)

Polymorphic Inductive word : Type :=
| fromStr : string -> word
| _inj : forall (t:Type), t -> word.
Polymorphic Coercion fromStr : string >-> word.

Polymorphic Class Split (s:string) (l:list word).
Polymorphic Instance drop_space {s l}`(Split s l) : Split (String " " s) l.
(* ASCII space character is decimal 32, octal 040, hex 0x20 --- bit 6/8 (bit 5) is the only bit set.  Need to parse any groups of characters containing no space.
    Could do this by doing splits for all n-length letter permutations, or by trying to be clever about bit sets.
    I *think* Coq's ascii library puts high order bits on the right
 *)
Polymorphic Class NotSpace (a:ascii).
Polymorphic Instance NotSpace0 {b1 b2 b3 b4 b5 b6 b7} : NotSpace (Ascii true b1 b2 b3 b4 b5 b6 b7).
Polymorphic Instance NotSpace1 {b0 b2 b3 b4 b5 b6 b7} : NotSpace (Ascii b0 true b2 b3 b4 b5 b6 b7).
Polymorphic Instance NotSpace2 {b0 b1 b3 b4 b5 b6 b7} : NotSpace (Ascii b0 b1 true b3 b4 b5 b6 b7).
Polymorphic Instance NotSpace3 {b0 b1 b2 b4 b5 b6 b7} : NotSpace (Ascii b0 b1 b2 true b4 b5 b6 b7).
Polymorphic Instance NotSpace4 {b0 b1 b2 b3 b5 b6 b7} : NotSpace (Ascii b0 b1 b2 b3 true b5 b6 b7).
Polymorphic Instance NotSpace5 {b0 b1 b2 b3 b4 b6 b7} : NotSpace (Ascii b0 b1 b2 b3 b4 false b6 b7).
Polymorphic Instance NotSpace6 {b0 b1 b2 b3 b4 b5 b7} : NotSpace (Ascii b0 b1 b2 b3 b4 b5 true b7).
Polymorphic Instance NotSpace7 {b0 b1 b2 b3 b4 b5 b6} : NotSpace (Ascii b0 b1 b2 b3 b4 b5 b6 true).

Goal NotSpace "W"%char. typeclasses eauto. Qed.

(** Not in love with this by-length specialization, but trying to parse with an intermediate "partial word"
    seems to have the same issue (or the need to do reverse, which then won't unify right later) *)
Polymorphic Instance split1 {c s l}`(NotSpace c)`(Split s l) : Split (String c (String " " s)) ([fromStr (String c EmptyString)] ++ l).
Polymorphic Instance split1' {c}`(NotSpace c) : Split (String c EmptyString) ([fromStr (String c EmptyString)]).
Polymorphic Instance split2 {c1 c2 s l}`(NotSpace c1)`(NotSpace c2)`(Split s l) : 
    Split (String c1 (String c2 (String " " s))) ([fromStr (String c1 (String c2 EmptyString))] ++ l).
Polymorphic Instance split2' {c1 c2}`(NotSpace c1)`(NotSpace c2) : 
    Split (String c1 (String c2 EmptyString)) ([fromStr (String c1 (String c2 EmptyString))]).
Polymorphic Instance split3  {c1 c2 c3 s l}`(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(Split s l) : Split (String c1 (String c2 (String c3 (String " " s)))) ([fromStr (String c1 (String c2 (String c3 EmptyString)))] ++ l).
Polymorphic Instance split3' {c1 c2 c3}    `(NotSpace c1)`(NotSpace c2)`(NotSpace c3)             : Split (String c1 (String c2 (String c3 EmptyString)))    ([fromStr (String c1 (String c2 (String c3 EmptyString)))]).
Polymorphic Instance split4  {c1 c2 c3 c4 s l}`(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)`(Split s l) : Split (String c1 (String c2 (String c3 (String c4 (String " " s))))) ([fromStr (String c1 (String c2 (String c3 (String c4 EmptyString))))] ++ l).
Polymorphic Instance split4' {c1 c2 c3 c4}    `(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)             : Split (String c1 (String c2 (String c3 (String c4 EmptyString))))    ([fromStr (String c1 (String c2 (String c3 (String c4 EmptyString))))]).
Polymorphic Instance split5  {c1 c2 c3 c4 c5 s l}`(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)`(NotSpace c5)`(Split s l) : Split (String c1 (String c2 (String c3 (String c4 (String c5 (String " " s)))))) ([fromStr (String c1 (String c2 (String c3 (String c4 (String c5 EmptyString)))))] ++ l).
Polymorphic Instance split5' {c1 c2 c3 c4 c5}    `(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)`(NotSpace c5)             : Split (String c1 (String c2 (String c3 (String c4 (String c5 EmptyString)))))    ([fromStr (String c1 (String c2 (String c3 (String c4 (String c5 EmptyString)))))]).
Polymorphic Instance split6  {c1 c2 c3 c4 c5 c6 s l}`(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)`(NotSpace c5)`(NotSpace c6)`(Split s l) : Split (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String " " s))))))) ([fromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 EmptyString))))))] ++ l).
Polymorphic Instance split6' {c1 c2 c3 c4 c5 c6}    `(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)`(NotSpace c5)`(NotSpace c6)             : Split (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 EmptyString))))))    ([fromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 EmptyString))))))]).
Polymorphic Instance split7  {c1 c2 c3 c4 c5 c6 c7 s l}`(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)`(NotSpace c5)`(NotSpace c6)`(NotSpace c7)`(Split s l) : Split (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String " " s)))))))) ([fromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 EmptyString)))))))] ++ l).
Polymorphic Instance split7' {c1 c2 c3 c4 c5 c6 c7}    `(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)`(NotSpace c5)`(NotSpace c6)`(NotSpace c7)             : Split (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 EmptyString)))))))    ([fromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 EmptyString)))))))]).
Polymorphic Instance split8  {c1 c2 c3 c4 c5 c6 c7 c8 s l}`(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)`(NotSpace c5)`(NotSpace c6)`(NotSpace c7)`(NotSpace c8)`(Split s l) : Split (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String c8 (String " " s))))))))) ([fromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String c8 EmptyString))))))))] ++ l).
Polymorphic Instance split8' {c1 c2 c3 c4 c5 c6 c7 c8}    `(NotSpace c1)`(NotSpace c2)`(NotSpace c3)`(NotSpace c4)`(NotSpace c5)`(NotSpace c6)`(NotSpace c7)`(NotSpace c8)             : Split (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String c8 EmptyString))))))))    ([fromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String c8 EmptyString))))))))]).


Polymorphic Class StringWords (ss : list string) (ws : list word).
Polymorphic Instance nilStringWords : StringWords nil nil.
Polymorphic Instance consStringWords {s ss ws}(sw:StringWords ss ws) : StringWords (s::ss) ((fromStr s)::ws).
