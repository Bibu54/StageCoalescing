-------------------------- MODULE TestAbstraction --------------------------

EXTENDS Integers, FiniteSetTheorems, WellFoundedInduction, TLAPS

----------------------------------------------------------------------------

\* Exemples

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

\* Mais c'est embêtant non ?

----------------------------------------------------------------------------

\* Problème lors de l'abstraction :

(*
On rencontre un problème lors de l'abstraction de sous-formules vers la logique
du premier ordre (donc avant envoi vers des prouveurs de logique classique).
Des sous-formules temporelles qui devraient être abstraites par un même prédicat
sont en fait abstraites vers des prédicats différents.
La formule n'est donc plus valide et ne peut plus être prouvée.
*)

\* Ce théorème est prouvé correctement
THEOREM ASSUME NEW S, NEW z, TEMPORAL P(_)
        PROVE (\A x \in S \cup {z} : P(x)) <=> (P(z) /\ \A x \in S : P(x))
        OBVIOUS

\* Celui-ci non
THEOREM ASSUME NEW S, NEW z, TEMPORAL P(_)
        PROVE (\A x \in S \cup {z} : <>P(x)) <=> (<>P(z) /\ \A x \in S : <>P(x))
        OBVIOUS
\* Ça ne fonctionne pas non plus avec []

(*
Selon l'article, les deux formules <>P(x) et <>P(y) devraient être
abstraites par [\lambda x . <>P(x)](x) et [\lambda y . <>P(y)](y)
par définition de l'abstraction d'un symbole <>.
(où [...] représente ... encadré)
La formule FOL obtenue est donc valide et devrait être prouvable,
puisqu'il s'agit de la même que pour le théorème précédent.
*)


\* On peut généraliser ce problème :

\* Fonctionne
THEOREM ASSUME NEW z, TEMPORAL P(_)
        PROVE (\A x : P(x)) => P(z)
        OBVIOUS

\* Ne fonctionne pas
THEOREM ASSUME NEW z, TEMPORAL P(_)
        PROVE (\A x : <>P(x)) => <>P(z)
        OBVIOUS
\* Ni avec []


\* On cherche la cause en bidouillant.

\* En plaçant z dans la formule :

\* Fonctionne toujours
THEOREM ASSUME TEMPORAL P(_)
        PROVE \A z : (\A x : P(x)) => P(z)
        OBVIOUS

\* Ne fonctionne pas non plus
THEOREM ASSUME TEMPORAL P(_)
        PROVE \A z : (\A x : <>P(x)) => <>P(z)
        OBVIOUS


\* De même avec \E :

\* Fonctionne
THEOREM ASSUME NEW z, TEMPORAL P(_)
        PROVE P(z) => (\E x : P(x))
        OBVIOUS

\* Ne fonctionne pas
THEOREM ASSUME NEW z, TEMPORAL P(_)
        PROVE ([]P(z)) => (\E x : []P(x))
        OBVIOUS

(* On cherche à comprendre pourquoi (au moins quand) les sous-formules temporelles
 * qui devraient être abstraites par un même prédicat ne le sont pas.
 * Les tests suivants fournissent des exemples où les sous-formules temporelles "identiques"
 * sont effectivements abstraites en des prédicats identiques avant d'être reléguées au
 * prouveur, ou pas.   *)

\* Fonctionne (comme observé précédemment sans symbole [] ni <>)
THEOREM ASSUME TEMPORAL P(_), TEMPORAL Q(_)
        PROVE ((\A x : P(x)) /\ (\A x : Q(x))) => (\A x : P(x) /\ Q(x))
        OBVIOUS

\* Fonctionne
THEOREM ASSUME TEMPORAL P(_), TEMPORAL Q(_)
        PROVE ((\A x : []P(x)) /\ (\A x : []Q(x))) => (\A x : ([]P(x)) /\ ([]Q(x)))
        OBVIOUS

\* Fonctionne : ce n'est pas une question d'alpha-renommage
THEOREM ASSUME TEMPORAL P(_), TEMPORAL Q(_)
        PROVE ((\A y : []P(y)) /\ (\A z : []Q(z))) => (\A x : ([]P(x)) /\ ([]Q(x)))
        OBVIOUS



\* Les deux exemples suivants sont assez étranges puisqu'il s'agit exactement des mêmes hypothèses.

\* Fonctionne
THEOREM ASSUME NEW P(_), NEW Q(_)
        PROVE (\A y : ([]P(y)) /\ (\A z : []Q(z))) => (\A x : ([]P(x)) /\ ([]Q(x)))
        OBVIOUS

\* Ne fonctionne pas
THEOREM ASSUME NEW P(_), NEW Q(_), (\A y : ([]P(y)) /\ (\A z : []Q(z)))
        PROVE (\A x : ([]P(x)) /\ ([]Q(x)))
        OBVIOUS


\* Sans les symboles [], cet effet ne se produit pas

\* Fonctionne
THEOREM ASSUME NEW P(_), NEW Q(_)
        PROVE (\A y : (P(y)) /\ (\A z : Q(z))) => (\A x : (P(x)) /\ (Q(x)))
        OBVIOUS

\* Fonctionne aussi
THEOREM ASSUME NEW P(_), NEW Q(_), (\A y : (P(y)) /\ (\A z : Q(z)))
        PROVE (\A x : (P(x)) /\ (Q(x)))
        OBVIOUS


\* On obtient le même résultat en remplaçant les prédicats constants par des opérateurs flexibles

\* Fonctionne
THEOREM ASSUME TEMPORAL P(_), TEMPORAL Q(_)
        PROVE (\A y : ([]P(y)) /\ (\A z : []Q(z))) => (\A x : ([]P(x)) /\ ([]Q(x)))
        OBVIOUS

\* Ne fonctionne pas
THEOREM ASSUME TEMPORAL P(_), TEMPORAL Q(_), (\A y : ([]P(y)) /\ (\A z : []Q(z)))
        PROVE (\A x : ([]P(x)) /\ ([]Q(x)))
        OBVIOUS

-----------------------------------------------------------------------------

\* TESTS LOGIQUE TEMPORELLE

(*
J'ai fait les tests suivants pour tester ce qu'était capable de prouver ou non
le prouveur pour la logique temporelle
*)

\* Les théorèmes suivants sont prouvés correctement
THEOREM ASSUME NEW P, NEW Q, P, Q
        PROVE P /\ Q
        BY PTL

THEOREM ASSUME NEW P, NEW Q, P
        PROVE P \/ Q
        BY PTL

THEOREM ASSUME TEMPORAL P
        PROVE P => P
        BY PTL
        
THEOREM ASSUME TEMPORAL P
        PROVE P => <>P
        BY PTL

THEOREM ASSUME TEMPORAL P, TEMPORAL Q, TEMPORAL R
        PROVE ((P ~> Q) /\ (Q ~> R)) => (P ~> R)
        BY PTL

THEOREM ASSUME TEMPORAL P
        PROVE (\neg \neg P) => P
        BY PTL


\* Les théorèmes suivants ne sont pas prouvés correctement

\* PTL ne gère pas l'arithmétique
THEOREM 4 = 2 + 2
    BY PTL

\* Tout va bien
THEOREM ASSUME TEMPORAL P
        PROVE P => []P
        BY PTL

\* Conclusion : PTL arrive à gérer
\*  /\, \/, \neg, =>

---------------------------------------------------------------------------------------

\* Assez étrange

\* Ne fonctionne pas
THEOREM ASSUME CONSTANT P
        PROVE P => []P
        BY PTL
        
\* Fonctionne
THEOREM ASSUME CONSTANT P, P
        PROVE []P
        BY PTL
-----------------------------------------------------------------------------

\* Comportement du prouveur PTL avec ou sans hypothèses flexibles

(* Ici :
 *  - SUFFICES P est accepté (pas normal a priori),
 *  - QED non (normal)  *)
THEOREM ASSUME TEMPORAL P \* , CONSTANT Q, Q, TEMPORAL R, []R
        PROVE []P
        <1>. SUFFICES P
             BY PTL
        <1>. QED
             OBVIOUS

(* En ajoutant P en hypothèse :
 *  - SUFFICES P n'est pas accepté,
 *  - QED est accepté
 * En fait le prouveur prend implicitement comme hypothèses toute formule
 * de la forme P => []P
 * lorsque le contexte ne contient que des hypothèses rigides
 * (même si c'est une explication intuitive)  *)
THEOREM ASSUME TEMPORAL P, P
        PROVE []P
        <1>. SUFFICES P
             BY PTL
        <1>. QED
             OBVIOUS

-------------------------------------------------------------------------------------

\* Transformation de formule avant abstraction des sous-formules

\* Valide et prouvable
THEOREM ASSUME NEW P(_)
        PROVE (\A x : <>P(x)) => <>(\A x : P(x))
        OBVIOUS

\* Idem
THEOREM ASSUME NEW P(_)
        PROVE <>(\A x : P(x)) => (\A x : <>P(x))
        OBVIOUS

\* Valide et prouvable
THEOREM ASSUME NEW P(_)
        PROVE (\A x : []P(x)) => [](\A x : P(x))
        OBVIOUS

\* Idem
THEOREM ASSUME NEW P(_)
        PROVE [](\A x : P(x)) => (\A x : []P(x))
        OBVIOUS

\* Valide mais non prouvable
THEOREM ASSUME TEMPORAL P(_)
        PROVE (\E x : []P(x)) => [](\E x : P(x))
        OBVIOUS

\* Non valide et non prouvable
THEOREM ASSUME TEMPORAL P(_)
        PROVE [](\E x : P(x)) => (\E x : []P(x))
        OBVIOUS


(*
On essaie d'observer les limites de l'implémentation actuelle de la transformation de formule
en essayant de prouver les formules valides suivantes :
*)

\* Fonctionne
THEOREM ASSUME NEW P(_,_)
        PROVE ([](\A x : [](\A y : P(x,y)))) => (\A x : [][](\A y : P(x,y)))
        OBVIOUS

\* Ne fonctionne pas, c'est bizarre car il s'agit des mêmes hypothèse et conclusion
THEOREM ASSUME NEW P(_,_), ([](\A x : [](\A y : P(x,y))))
        PROVE (\A x : [][](\A y : P(x,y)))
        OBVIOUS

(* Ne fonctionne pas, le prouveur n'essaie pas de transformer des sous-formules
 * en dessous d'un symbole []    *)
THEOREM ASSUME NEW P(_,_)
        PROVE ([](\A x : [](\A y : P(x,y)))) => (\A x : \A y : [][]P(x,y))
        OBVIOUS

\* Idem
THEOREM ASSUME NEW P(_,_), ([](\A x : [](\A y : P(x,y))))
        PROVE (\A x : \A y : [][]P(x,y))
        OBVIOUS

(*
Une question intéressante serait de savoir si on peut généraliser la réécriture
des formules en ajoutant des règles supplémentaires préservant la validité.
Parmi celles déjà implémentées :
[]\A x : ... <=> \A x : []...
<>\A x : ... <=> \A x : <>...
On pourrait en rajouter certaines concernant \E.
On pourrait également transformer des symboles logiques, afin qu'ils soient
abstraits de la même manière.
Par exemple :
A ~> B <=> [](A => <>B)
<>A <=> \neg [] \neg A
\E <=> \neg <> \neg A
La dernière règle n'est pas utile lors d'une transformation avant traitement
de la formule par un prouveur de logique classique, mais le devient lors d'une
transformation destinée à un prouveur de logique temporelle, et inversement
pour l'avant dernière règle.

Une autre idée serait d'effectuer cette transformation sur toutes
les sous formules, y compris se trouvant sous un symbole devant être abstrait.
Par exemple :

[]\A x : P(x) => \A x : []P(x)

est actuellement prouvable avec OBVIOUS (transformation, abstraction puis
envoi au prouveur), mais

[][]\A x : P(x) => [] \A x : []P(x)

ne l'est pas.

Enfin une dernière idée est d'abstraire vers un même prédicat des formules
identiques modulo symétrie de l'égalité. (c'est peut-être déjà implémenté)
*)

=============================================================================
\* Modification History
\* Last modified Tue Jun 16 20:16:11 CEST 2020 by raphael
\* Created Mon Jun 15 10:15:33 CEST 2020 by raphael
