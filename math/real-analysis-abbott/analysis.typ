//**** init-ting
#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *real analysis*
  ],
  authors: (
    (
      name: "mkh",
    ),
  ),
  abstract: [
    self-study notes of real analysis---based primarily on _Understanding Analysis_ by Abbott.
  ],
)

#include "chpt/chpt-1.typ"
