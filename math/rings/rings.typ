//**** init-ting
#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *ring theory*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on ring theory, inspired heavily by Dexter Chua's Cambridge notes -- essentially just these rewritten in Typst with some stuff added/removed.
  ],
)

= Introduction
In rings we are allowed to add, subtract and multiply but not divide. The canonical example of a ring would be $ZZ$, the integers.

We'll only consider rings in which multiplication is commutative, since these behave like number systems. We'd like to understand $ZZ$, and whether certain properties of $ZZ$ is present in other arbitrary rings, and how these properties relate.

#include "chpt/chpt-1.typ"
