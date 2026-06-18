#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *point-set topology notes*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on basic topology and some metric stuff.
  ],
)

#include "chpt/chpt-1.typ"
#include "chpt/chpt-2.typ"
#include "chpt/chpt-3.typ"
