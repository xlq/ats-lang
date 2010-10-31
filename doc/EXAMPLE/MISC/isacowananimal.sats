(*
**
** An interesting example found at http://merd.sourceforge.net
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2010
**
*)

//
// HX: note that this is just a specification
//

(* ****** ****** *)
//
datasort thing = (* abstract *)
//
(* ****** ****** *)

sta cow: thing
sta rabbit: thing
sta human: thing

dataprop ANIM (thing) =
  | ANIMcow (cow)
  | ANIMrabbit (rabbit)
  | ANIMhuman (human)
// end of [ANIM]

(* ****** ****** *)

sta grass: thing
sta carrot: thing

dataprop VEGE (thing) =
  | VEGEgrass (grass) | VEGEcarrot (carrot)
// end of [VEGE]

(* ****** ****** *)

sta beef: thing
sta dead_rabbit: thing
sta dead_human: thing

dataprop MEAT (thing) =
  | MEATbeef (beef)
  | MEATdead_rabbit (dead_rabbit)
  | MEATdead_human (dead_human)
// end of [MEAT]

(* ****** ****** *)

dataprop AF ( // Animal/Food relation
  thing(*animal*), thing(*food*)
) =
  | AFcow (cow, grass)
  | AFrabbit (rabbit, carrot)
  | AFhuman1 (human, carrot)
  | {x:thing} AFhuman2 (human, x) of MEAT (x) // human eats any meat
// end of [AF]

(* ****** ****** *)

dataprop AM ( // Animal/Meat relation
  thing(*animal*), thing(*meat*)
) =
  | AMcow (cow, beef)
  | AMrabbit (rabbit, dead_rabbit)
  | AMhuman (human, dead_human)
// end of [AM]

(* ****** ****** *)

absviewtype THING (thing)
//
// HX: everything has some energy
//
fun get_energy {x:thing} (X: THING (x)): int

(* ****** ****** *)
//
// HX: slaughering an animal turns it into some meat
//
fun slaughter {x:thing}
  (pf: ANIM (x) | X: THING(x)): [y:thing] (AM (x, y) | THING y)
// end of [slaughter]

(* ****** ****** *)

absviewtype EATEN (thing)

prfun eaten_once {x:thing}
  (X: EATEN (x)): void // thing can only be eaten once
prfun eaten_more {x:thing}
  (pf: VEGE (x) | X: !EATEN (x) >> THING (x)): void // vegetable can be eaten repeatedly

(* ****** ****** *)

fun eat_animal_food {x1,x2:thing}
  (pf: AF (x1, x2) | A: !THING (x1), F: !THING (x2) >> EATEN(x2)): void
// end of [eat_animal_food]

(* ****** ****** *)

(* end of [isacowananimal.sats] *)
