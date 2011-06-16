
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

(* Rotaties per seconde van de as die de molenstenen aandraait,
   en de schuddebak van energie voorziet *)
Variable rotatie: Z.
Axiom Natuurlijk2: rotatie >= 0.

Variable TODO: B.

(*
    Predikaten GA, GB, GC
    GA t g: Er is {g} gram graan op tijdstip {t} aanwezig op plek A
    - A: onderaan de lift
    - B: bovenaan de lift
    - C: invoer molenstenen
*)
Variables GA GB GC: T -> G -> B.

(*
    Predikaten MD, ME
    MD t m: Er is {m} gram meel op tijdstip {t} aanwezig op plek D
    - D: bovenaan de meelpijp
    - E: invoer zak
    - Z: in de zak -- deze wordt gebruikt in Molenaar
*)
Variables MD ME MZ: T -> M -> B.

(*
    Predikaat ZF
    ZF t z: Op tijdstip {t} zijn er {z} zakken volledig gevuld
*)
Variable  ZF:       T -> Z -> B.

(* Constanten > Algemeen *)
Definition maxSec := 60 * 60 * 24. (* Aantal seconden in een dag *)
Definition rMin := 20. (* Minimale rotatie *)

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

(*
    IN:  stroom, GA
    UIT: GB
*)
Definition Elevator :=
  stroom -> (
    forall t:T, (exists k:Z, k >= 0 /\ t = k * eD) -> (
        (* Elke {eD} sec wordt {eG} gram graan meegenomen door de elevator *)
        (forall g:G, g%Z >= eG -> GA t g -> GA (t + eD) (g - eG))
     /\ (forall g:G, g >= 0  -> GA t g -> GA (t + eD) 0)
        (* Elke {eTD} sec later arriveert deze bovenaan *)
     /\ (forall g:G, g >= eG -> (forall gb:G,
            GA t g /\ GB (t + eTD-eD) gb ->  GB (t + eTD) (gb + eG)))
     /\ (forall g:G, g >= 0  -> (forall gb:G,
            GA t g /\ GB (t + eTD-eD) gb ->  GB (t + eTD) (gb + g)))
        (* Alle tijdstippen tussen n*eD en (n+1)*eD *)
     /\ (forall g:G, forall s:T, (s >= t /\ s < t+eD) ->
            (GA s g <-> GA t g) /\ (GB s g <-> GB t g))
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

(*
    IN:  MD
    UIT: ME
*)
Definition Meelpijp :=
    (MD 0 0) /\
    (ME 0 0) /\
    (forall t:T, forall m:M,
        (m > pCap -> MD t m -> ME (t + pTD) pCap)
     /\ (m < pCap -> MD t m -> ME (t + pTD) m)
    ).

(*
    IN:  ME
    UIT: ZF
*)
Definition Molenaar :=
    (* Begintoestand: nog geen meel in zak, nog geen gevulde zakken *)
    (MZ 0 0) /\
    (ZF 0 0) /\
    (* De zak mag nooit overstromen *)
    ~(exists t:T, exists m:M, MZ t m /\ m >= zMax) /\
    (* Verder geldt dat.. *)
    (forall t:T, forall mprev:M, forall madd:M, forall zprev:ZAKKEN,
        (MZ t mprev /\ ME t madd /\ ZF t zprev)
     -> (
            (* Zak wordt enkel bijgevuld door toevoer stroom meel *)
            (                 MZ (t + 1) (mprev + madd) /\ ZF (t + 1) zprev) \/
            (* OF, indien al meer dan {zMin} meel in zak, nieuwe zak! *)
            (mprev >= zMin /\ MZ (t + 1) madd           /\ ZF (t + 1) (zprev + 1))
        )
    ).

(*
    Specificatie van het geheel
    IN:  stroom, rotatie, GA
    UIT: ZF
*)
Definition Geheel := TODO.
