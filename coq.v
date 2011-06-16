
(* Types > Verzamelingen *)
Definition T := Z. (* Tijdstippen na start werk *)
Definition G := Z. (* Hoeveelheid graan in gram *)
Definition M := Z. (* Hoeveelheid meel in gram *)
Definition ZAKKEN := Z. (* Aantal gevulde zakken *)
(* Ik wil met natuurlijke getallen werken, maar Coq geeft dan veel problemen,
   dus los ik het natuurlijk gewoon zo op: *)
Open Scope Z_scope.
Axiom Natuurlijk: (forall x:T, x >= 0) /\ (forall x:G, x >= 0)
               /\ (forall x:M, x >= 0) /\ (forall x:ZAKKEN, x >= 0).

(* Of er (genoeg, etc) stroom naar de elevator gaat *)
Variable stroom: B.

Variable TODO: B.

Variables graan kaap geschud:    T -> G -> B.
Variables gemalen naarzak inzak: T -> M -> B.
Variable  zakken:                T -> Z -> B.

(* Constanten > Algemeen *)
Definition maxSec := 60 * 60 * 24. (* Aantal seconden in een dag *)

(* Constanten > Elevator *)
Definition eD:T  := 3%Z.   (* tijd tot volgende bak *)
Definition eG:G  := 500%Z. (* hoeveelheid graan per bak *)
Definition eTD:G := 30%Z.  (* tijd tot bak boven is *)

(* Constanten > Meelpijp *)
Definition pCap:M := 200. (* De capaciteit, dus de maximale hoeveelheid meel, dat per seconde door de meelpijp kan *)
Definition pTD:T  := 5.   (* De tijdsduur die het duurt tot meel van de ingang naar de uitgang van de meelpijp gaat *)

(* Constanten > Molenaar *)
Definition zMin:M := 15000. (* Minimale meel in zak (inclusief) *)
Definition zMax:M := 25000. (* Maximale meel in zak (exclusief) *)

Definition Elevator :=
  stroom -> (
    forall t:T, (exists k:Z, k >= 0 /\ t = k * eD) ->
    (
        (* Elke {eD} sec wordt {eG} gram graan meegenomen door de elevator *)
        (forall g:G, (g > eG  -> graan t g -> graan (t + eD) (g - eG))
                  /\ (g <= eG -> graan t g -> graan (t + eD) 0)
        )
        
        (* Elke {eTD} sec later arriveert deze bovenaan *)
     /\ (forall g:G, g > eG  -> (forall gk:G, graan t g /\ kaap (t + eTD - eD) gk -> kaap (t + eTD) (gk + eG))
                  /\ g <= eG -> (forall gk:G, graan t g /\ kaap (t + eTD - eD) gk -> kaap (t + eTD) (gk + g))
        )
        
        (* Alle tijdstippen tussen n*eD en (n+1)*eD *)
     /\ (forall g:G, forall s:T, (s >= t /\ s < t+eD) ->
            (graan s g <-> graan t g) /\ (kaap s g <-> kaap t g))
  ))
.

(*
    IN:  rotatie, GB
    UIT: GC
*)
Definition Schuddebak := TODO.

(*
    IN:  rotatie, GC
    UIT: MD
*)
Definition Molenstenen := TODO.

Definition Meelpijp :=
    (gemalen 0 0) /\
    (naarzak 0 0) /\
    (forall t:T, forall m:M,
        (m > pCap -> gemalen t m -> naarzak (t + pTD) pCap)
     /\ (m < pCap -> gemalen t m -> naarzak (t + pTD) m)
    ).

Definition Molenaar :=
    (* Begintoestand: nog geen meel in zak, nog geen gevulde zakken *)
    (inzak 0 0) /\
    (zakken 0 0) /\
    (* De zak mag nooit overstromen *)
    ~(exists t:T, exists m:M, inzak t m /\ m >= zMax) /\
    (* Verder geldt dat.. *)
    (forall t:T, forall mprev:M, forall madd:M, forall zprev:ZAKKEN,
        (inzak t mprev /\ naarzak t madd /\ zakken t zprev)
     -> (
            (* Zak wordt enkel bijgevuld door toevoer stroom meel *)
            (                 inzak (t + 1) (mprev + madd) /\ zakken (t + 1) zprev) \/
            (* OF, indien al meer dan {zMin} meel in zak, nieuwe zak! *)
            (mprev >= zMin /\ inzak (t + 1) madd           /\ zakken (t + 1) (zprev + 1))
        )
    ).

(*
    Specificatie van het geheel
    IN:  stroom, rotatie, GA
    UIT: ZF
*)
Definition Geheel := TODO.
