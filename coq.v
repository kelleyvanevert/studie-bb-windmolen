
(* Types > Verzamelingen *)
Definition T := Z. (* Tijdstippen na start werk *)
Definition G := Z. (* Hoeveelheid graan in gram *)
Definition M := Z. (* Hoeveelheid meel in gram *)
Definition Z := Z. (* Aantal gevulde zakken *)
(* Ik wil met natuurlijke getallen werken, maar Coq geeft dan veel problemen,
   dus los ik het natuurlijk gewoon zo op: *)
Open Scope Z_scope.
Axiom Natuurlijk: (forall x:T, x >= 0) /\ (forall x:G, x >= 0)
               /\ (forall x:M, x >= 0) /\ (forall x:Z, x >= 0).

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
    - D: bovenaan de pijp
    - E: invoer zak
*)
Variables MD ME:    T -> M -> B.

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
Definition Pijp := TODO.

(*
    IN:  ME
    UIT: ZF
*)
Definition Molenaar := TODO.

(*
    Specificatie van het geheel
    IN:  stroom, rotatie, GA
    UIT: ZF
*)
Definition Geheel := TODO.
