//**** init-ting
#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *measure theory*
  ],
  authors: (
    (
      name: "mkh",
    ),
  ),
  abstract: [
    self-study notes of measure theory---based primarily on _Measures, Integrals and Martingales_ by Schilling.
  ],
)

#include "chpt/chpt-1.typ"
