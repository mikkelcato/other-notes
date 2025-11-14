//**** init-ting
#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *introductory differential geometry*
  ],
  authors: (
    (
      name: "mkh",
    ),
  ),
  abstract: [
    self-study notes of basic differential geometry (and Riemannian geometry) for physics---based on David Tong's GR notes and Sean Carroll's GR notes.
  ],
)

#include "chpt/chpt-1.typ"
