------------------------------- MODULE FOLTL --------------------------------
(***************************************************************************)
(* Experiments with proofs about first-order temporal logic.               *)
(***************************************************************************)
EXTENDS Integers, FiniteSetTheorems, WellFoundedInduction, TLAPS

(***************************************************************************)
(* The following theorem has a temporal flavor but in fact A(_) is         *)
(* declared as a constant, and the proof obligation passed to the          *)
(* backend provers is a simple tautology.                                  *)
(***************************************************************************)
THEOREM ForallBoxConstant ==
  ASSUME NEW A(_), NEW S
  PROVE  (\A x \in S : []A(x)) <=> [](\A x \in S : A(x))
OBVIOUS

(***************************************************************************)
(* The analogous theorem for a temporal formula A(_) is also proved        *)
(* automatically because the coalescing algorithm knows that universal     *)
(* quantification commutes with [].                                        *)
(***************************************************************************)
THEOREM ForallBoxTemporal ==
  ASSUME TEMPORAL A(_), NEW S
  PROVE  (\A x \in S : []A(x)) <=> [](\A x \in S : A(x))
OBVIOUS

(***************************************************************************)
(* As a concrete example of the above, we can prove the following theorem. *)
(***************************************************************************)
THEOREM ASSUME NEW n \in Nat, STATE x
        PROVE  (\A i \in 1..n : []<>(x=i)) <=> [](\A i \in 1..n : <>(x=i))
OBVIOUS

\* Exercise: try to prove the above using theorem ForallBoxTemporal
THEOREM ASSUME NEW n \in Nat, STATE x
        PROVE  (\A i \in 1..n : []<>(x=i)) <=> [](\A i \in 1..n : <>(x=i))
    BY ForallBoxTemporal
    
(***************************************************************************)
(* Attempting to prove the analogue of ForallBoxTemporal for a set S that  *)
(* is not constant fails, as it should (use C-G C-P).                      *)
(* However, there is a FINGERPRINTING BUG that identifies the statement    *)
(* with the one of theorem ForallBoxConstant, and therefore C-G C-G claims *)
(* that the theorem is proved!                                             *)
(***************************************************************************)
THEOREM ASSUME TEMPORAL A(_), STATE S
        PROVE  (\A x \in S : []A(x)) <=> [](\A x \in S : A(x))
OBVIOUS

-----------------------------------------------------------------------------

(***************************************************************************)
(* The following theorem asserts that quantification over a finite         *)
(* constants set commutes with <>[]. (The axiom STL6 from the TLA paper    *)
(* asserts this for a conjunction of two formulas, hence the name of the   *)
(* theorem.) Note that finiteness is essential here.                       *)
(***************************************************************************)
THEOREM STL6_gen ==
  ASSUME NEW S, IsFiniteSet(S), TEMPORAL F(_)
  PROVE  (\A x \in S : <>[]F(x)) <=> <>[](\A x \in S : F(x))
<1>. DEFINE G(T) == (\A x \in T : <>[]F(x)) <=> <>[](\A x \in T : F(x))
<1>1. G({})
  <2>1. \A x \in {} : F(x)  OBVIOUS
  <2>2. <>[](\A x \in {} : F(x))  BY <2>1, PTL
  <2>. QED  BY <2>2
<1>2. ASSUME NEW T, NEW z
      PROVE  G(T) => G(T \cup {z})
  <2>1. (\A x \in T \cup {z} : <>[]F(x)) <=> <>[]F(z) /\ (\A x \in T : <>[]F(x))
    \* OBVIOUS fails due to coalescing problem
    <3>. DEFINE FF(x) == <>[]F(x)
    <3>. HIDE DEF FF
    <3>. (\A x \in T \cup {z} : FF(x)) <=> FF(z) /\ (\A x \in T : FF(x))
      OBVIOUS
    <3>. QED  BY DEF FF
  <2>2. <>[]F(z) /\ <>[](\A x \in T : F(x)) <=> <>[](F(z) /\ \A x \in T : F(x))
    BY PTL  \* instance of STL6
  <2>3. <>[](F(z) /\ \A x \in T : F(x)) <=> <>[](\A x \in T \cup {z} : F(x))
    <3>1. (F(z) /\ \A x \in T : F(x)) <=> (\A x \in T \cup {z} : F(x))
      OBVIOUS
    <3>. QED  BY <3>1, PTL
  <2>. QED  BY <2>1, <2>2, <2>3
<1>. QED
  <2>. HIDE DEF G
  <2>1. ASSUME NEW T, IsFiniteSet(T)  PROVE G(T)
    BY <1>1, <1>2, IsFiniteSet(T), FS_Induction, IsaM("blast")
  <2>2.G(S) BY <2>1  \* why does the proof fail without this step?
  <2>. QED  BY <2>2 DEF G
  

-----------------------------------------------------------------------------

(*
(* Inutile en fait.. *)
LEMMA BUVEUR ==
    ASSUME TEMPORAL P(_), TEMPORAL Q
    PROVE (((\E y : P(y)) => Q) => \E y : P(y) => Q)
    <1> DEFINE R == \E y : P(y)
    <1>1. ASSUME ((\E y : P(y)) => Q)
          PROVE \E y : P(y) => Q
          <2>1 R \/ \neg R
               <3> QED OBVIOUS
          <2>2. ASSUME R
                PROVE \E y : P(y) => Q
               <3>. QED  BY <2>2, <1>1
          <2>3. ASSUME \neg R
                PROVE \E y : P(y) => Q
               <3>1. ASSUME NEW y, P(y)
                     PROVE Q
                     <4> QED  BY <3>1, <2>3 DEF R
               <3>2. QED  BY <3>1
          <2> QED  BY <2>1, <2>2, <2>3
    <1> QED BY <1>1
*)

    
(***************************************************************************)
(* Exercise: complete the proof of the following theorem.                  *)
(* The LATTICE rule from the TLA paper underlies liveness proofs based     *)
(* on well-founded orderings.                                              *)
(***************************************************************************)
THEOREM LATTICE ==
  ASSUME NEW R, NEW S, IsWellFoundedOn(R,S), TEMPORAL F(_), TEMPORAL G
  PROVE  (\A x \in S : F(x) ~> (G \/ \E y \in SetLessThan(x,R,S) : F(y)))
         => \A x \in S : F(x) ~> G
<1>. DEFINE H(x) == F(x) ~> G
            LT(x) == F(x) ~> (G \/ \E y \in SetLessThan(x,R,S) : F(y))
<1>1. ASSUME NEW z \in S
      PROVE  (\A x \in S : LT(x))
             => ((\A y \in SetLessThan(z,R,S) : H(y)) => H(z))
  <2> DEFINE K(x) == F(x) ~> \E y \in SetLessThan(x,R,S) : F(y)
  <2>1. ASSUME (\A x \in S : LT(x)), 
               (\A y \in SetLessThan(z,R,S) : H(y))
        PROVE H(z)
    <3>. HIDE DEF LT
    <3>1. LT(z)
          BY <2>1, <1>1
    <3>2. \/ F(z) ~> G
          \/ F(z) ~> (\E y \in SetLessThan(z,R,S) : F(y))
          BY PTL, <2>1, <3>1 DEF LT
    <3>3. (\E y \in SetLessThan(z,R,S) : F(y)) ~> G
      <4> DEFINE T == SetLessThan(z,R,S)
      <4>1. \A y \in T : [](F(y) => <>G)
        BY <2>1, PTL DEF H
      <4>2. [](\A y \in T : F(y) => <>G)
        BY <4>1 \* coalescing ! :)
      <4>3. (\A y \in T : F(y) => <>G) => ((\E y \in T : F(y)) => <>G)
        OBVIOUS
      <4>4. []((\A y \in T : F(y) => <>G) => ((\E y \in T : F(y)) => <>G))
        \* BY <4>3, PTL
(*        \* comment montrer que pour P valide, []P est valide ?
        <5> DEFINE REC == ((\A y \in T : F(y) => <>G) => ((\E y \in T : F(y)) => <>G))
        <5> QED
*)
      <4>5. []((\E y \in T : F(y)) => <>G)
        BY PTL, <4>2, <4>4
      <4> QED  BY <4>5, PTL
    <3> QED  BY <3>2, <3>3, PTL
  <2> QED BY <2>1 DEF K
<1>2. QED
  <2>. HIDE DEF H
  <2>. (\A x \in S : LT(x)) => \A x \in S: H(x)
    BY <1>1, WFInduction, IsaM("blast")
  <2>. QED  BY DEF H

-----------------------------------------------------------------------------

(***************************************************************************)
(* We specify a simple decrement counter and use some of the above lemmas  *)
(* for proving properties.                                                 *)
(***************************************************************************)

VARIABLE cnt

Init == cnt \in Nat
Dec == cnt > 0 /\ cnt' = cnt-1
Spec == Init /\ [][Dec]_cnt /\ WF_cnt(Dec)

(***************************************************************************)
(* Exercise: prove the following theorems.                                 *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []Init
      <1> DEFINE Inv == Init
      <1>0. Init => Inv
          OBVIOUS
      <1>1. (Inv /\ Dec) => Inv'
          BY DEF Init, Dec, Nat, Inv
      <1>2. (Inv /\ UNCHANGED cnt) => Inv'
          BY DEF Inv, Init
      <1>3. (Init /\ [][Dec]_cnt) => []Inv
          BY PTL, <1>1, <1>2
      <1> QED  BY <1>3 DEF Spec

LEMMA Enable == (ENABLED << Dec >>_cnt) <=> cnt > 0

THEOREM Termination == Spec => <>(cnt = 0)

=============================================================================
